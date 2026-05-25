# Proof Reasoning

## Iteration 1: prove generated pure arithmetic and assertion witnesses

Fresh `symexec` succeeded on the current annotated file and generated three manual placeholders in `coq/generated/array_first_peak_proof_manual.v`:

```coq
Lemma proof_of_array_first_peak_safety_wit_2 : array_first_peak_safety_wit_2.
Proof. Admitted.

Lemma proof_of_array_first_peak_entail_wit_3 : array_first_peak_entail_wit_3.
Proof. Admitted.

Lemma proof_of_array_first_peak_return_wit_2 : array_first_peak_return_wit_2.
Proof. Admitted.
```

The corresponding goal definitions show that `safety_wit_2` only needs integer range facts for `i + 1` from `1 <= i`, `i <= n_pre + 1`, `0 <= n_pre`, and `Zlength l = n_pre`; this should be handled by `pre_process; entailer!; lia` because C `int` parameters and list lengths expose the needed boundedness facts through the generated context.

`entail_wit_3` is the loop-exit bridge from the invariant range to the postcondition range:

```coq
forall j, 0 < j /\ j < i -> not_peak j
|-- forall j, 0 < j /\ j + 1 < n_pre -> not_peak j
```

The missing step is arithmetic: from loop exit `i + 1 >= n_pre` and target guard `j + 1 < n_pre`, prove `j < i`, then apply the invariant hypothesis.

`return_wit_2` must choose the right side of the postcondition disjunction for the literal return value `-1`; after `Right`, the equality `-1 = -1` and the quantified no-peak fact are already present in the assertion produced by `entail_wit_3`.

Planned edit: replace only these three `Admitted.` bodies in `array_first_peak_proof_manual.v`, without changing generated goal or auto files. Then compile the generated files to confirm whether these tactics close the exact QCP assertion shape.

## Iteration 2: regenerated obligations after invariant strengthening

After strengthening the invariant for C-int safety and rerunning `symexec`, the manual file was regenerated and now contains:

```coq
Lemma proof_of_array_first_peak_entail_wit_1 : array_first_peak_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_first_peak_entail_wit_3 : array_first_peak_entail_wit_3.
Proof. Admitted.

Lemma proof_of_array_first_peak_return_wit_2 : array_first_peak_return_wit_2.
Proof. Admitted.
```

The new `entail_wit_1` is invariant initialization. It now includes `n_pre <= INT_MAX` and `1 + 1 <= INT_MAX`; a `coqtop` probe showed that `pre_process` closes the whole goal in this generated context:

```text
Lemma debug : array_first_peak_entail_wit_1.
Proof.
  pre_process.
  ...
No more goals.
```

The other two obligations retain the same proof shape as iteration 1. `entail_wit_3` still needs the arithmetic bridge from `j + 1 < n_pre` and `i + 1 >= n_pre` to `j < i`; `return_wit_2` still chooses the right disjunct for returning `-1`.

## Iteration 3: contract boundary on missing `n <= INT_MAX`

Compiling the iteration-2 proof bodies stopped at `proof_of_array_first_peak_entail_wit_1`:

```text
File ".../array_first_peak_proof_manual.v", line 24, characters 0-4:
Error: (in proof proof_of_array_first_peak_entail_wit_1):
Attempt to save an incomplete proof
```

The full `coqtop` state after `pre_process` is:

```coq
a_pre, n_pre : Z
l : list Z
H  : 0 <= n_pre
H0 : Zlength l = n_pre
============================
IntArray.full a_pre n_pre l
|-- [| n_pre <= 2147483647 |] && ...
```

This remaining goal is not derivable from the current formal contract. The input precondition has:

```c
0 <= n &&
Zlength(l) == n &&
IntArray::full(a, n, l)
```

but it does not state `n <= INT_MAX`. The program evaluates `i + 1` in the loop condition and later increments `i`; to prove those C-int safety obligations for all logical states allowed by the contract, the verifier needs an upper bound on `n`. Strengthening the invariant with `n <= INT_MAX` exposes the exact missing assumption at invariant initialization. Without that strengthening, the earlier generated `safety_wit_2` instead gets stuck on `i + 1 <= INT_MAX` from only `i <= n_pre + 1`, which is the same missing-bound issue one step later.

Because Verify is only allowed to add `Inv` / `Assert` / bridge annotations and must not rewrite the input `Require`, I cannot soundly finish this proof in the current workspace. A successful Contract-stage repair would add a bound such as `n <= INT_MAX` to the input precondition, matching nearby verified examples that perform `i + 1` or `i++` under an array length.

## Retry Iteration 4: prove regenerated preservation and return witnesses after narrowing the invariant

After removing the uninitializable `n <= INT_MAX` conjunct from the loop invariant and exit assertion, rerunning `symexec` succeeded and regenerated `coq/generated/array_first_peak_proof_manual.v` with four manual placeholders:

```coq
Lemma proof_of_array_first_peak_entail_wit_2_1 : array_first_peak_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_first_peak_entail_wit_2_2 : array_first_peak_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_first_peak_entail_wit_3 : array_first_peak_entail_wit_3.
Proof. Admitted.

Lemma proof_of_array_first_peak_return_wit_2 : array_first_peak_return_wit_2.
Proof. Admitted.
```

The initialization blocker `array_first_peak_entail_wit_1` disappeared. The new preservation witnesses both extend the processed-prefix fact from `j < i` to `j < i + 1`. A `coqtop` probe in `logs/coqtop_retry_entail_wit_2_1.log` showed that `pre_process` derives `n_pre <= 2147483647` from `IntArray.full a_pre n_pre l`, so the arithmetic conjunct `i + 1 + 1 <= INT_MAX` is no longer the blocker. After `entailer!`, the remaining semantic subgoal for `entail_wit_2_1` is:

```coq
H  : Znth i l 0 < Znth (i - 1) l 0
H5 : forall j, 0 < j < i ->
       Znth j l 0 < Znth (j - 1) l 0 \/
       Znth j l 0 < Znth (j + 1) l 0
============================
forall j, 0 < j < i + 1 ->
  Znth j l 0 < Znth (j - 1) l 0 \/
  Znth j l 0 < Znth (j + 1) l 0
```

The proof splits on `j < i`. If true, reuse the old prefix hypothesis. Otherwise, the range `0 < j < i + 1` implies `j = i`, and the current branch condition supplies the new no-peak fact. `entail_wit_2_2` has the same shape, but the current branch condition is `Znth i l 0 < Znth (i + 1) l 0`, so the `j = i` case proves the right disjunct.

The exit bridge `entail_wit_3` has:

```coq
H  : i + 1 >= n_pre
H4 : forall j_2, 0 < j_2 < i -> not_peak j_2
============================
forall j, 0 < j /\ j + 1 < n_pre -> not_peak j
```

Here the only missing step is arithmetic: `j + 1 < n_pre <= i + 1` gives `j < i`; then apply `H4`.

The `return_wit_2` proof chooses the right disjunct of the postcondition for the concrete return value `-1`; after `Right`, `entailer!` discharges `-1 = -1`, the quantified no-peak assertion, and the unchanged `IntArray.full` heap.

Planned edit: replace exactly the four `Admitted.` proof bodies in `array_first_peak_proof_manual.v` with the proof scripts validated in `logs/coqtop_retry_proof_attempts_2.log`. No helper lemma or axiom is needed.

## Retry Iteration 5: make the proof scripts independent of generated hypothesis numbers

The first batch compile after inserting the `coqtop`-validated proof scripts failed in `proof_of_array_first_peak_entail_wit_2_1`:

```text
File ".../array_first_peak_proof_manual.v", line 28, characters 14-15:
Error:
...
H4 : forall j : Z, 0 < j < i -> not_peak j
H5 : 0 <= n_pre
...
The term "j" has type "Z" while it is expected to have type
"(0 ?= n_pre)%Z = Gt".
```

The problem is not the proof idea; it is a fragile script detail. In the interactive probe, the old-prefix hypothesis was named `H5`, but in batch compilation the same hypothesis is named `H4`, while `H5` is `0 <= n_pre`. The proof therefore tried to apply the numeric fact as a function.

The concrete repair is to avoid generated names for the prefix hypothesis. In both preservation witnesses, after deriving `Hjrange : 0 < j /\ j < i`, use a `match goal` pattern:

```coq
match goal with
| Hprefix : forall k : Z, 0 < k /\ k < i -> _ |- _ =>
    exact (Hprefix j Hjrange)
end
```

This selects the prefix-preservation hypothesis by its type, regardless of whether `coqc` names it `H4`, `H5`, or `H6`. The current-index branch still uses `left; assumption` or `right; assumption`, which is stable because the target after selecting the disjunct exactly matches the branch condition in context. The exit bridge similarly should select the `forall k, 0 < k /\ k < i -> _` hypothesis by shape instead of assuming it is `H4`.

## Retry Iteration 6: confirmed boundary after pre-loop bridge attempt

The narrowed invariant was not sufficient: after `entailer!`, `logs/coqtop_retry_entail_2_1_current.log` left the arithmetic goal:

```coq
H0 : i + 1 < n_pre
H3 : i + 1 <= 2147483647
============================
i + 1 + 1 <= 2147483647
```

This needs `n_pre <= INT_MAX`. I then tried a Verify-only pre-loop assertion in the annotated C to materialize the fact from the C `int n` parameter before the loop:

```c
/*@ Assert
      1 <= i && i <= n + 1 &&
      n <= INT_MAX &&
      i + 1 <= INT_MAX &&
      ...
*/
```

However, rerunning `symexec` regenerated `array_first_peak_entail_wit_1` with the same unprovable shape:

```coq
forall a_pre n_pre l,
  [| 0 <= n_pre |] &&
  [| Zlength l = n_pre |] &&
  IntArray.full a_pre n_pre l
|--
  [| n_pre <= INT_MAX |] && ...
```

The final compile replay in `logs/compile_retry_20260422_final.log` fails at:

```text
File ".../array_first_peak_proof_manual.v", line 24, characters 0-4:
Error:
 (in proof proof_of_array_first_peak_entail_wit_1): Attempt to save an incomplete proof
(there are remaining open goals).
```

The current `proof_manual.v` no longer contains `Admitted.` in its manually edited text, but `proof_of_array_first_peak_entail_wit_1` intentionally remains as the incomplete `pre_process` proof that exposes the unsatisfied obligation. This is a confirmed contract boundary: the input `Require` does not provide `n <= INT_MAX`, and both possible annotation shapes need that fact either at invariant initialization or at preservation of the post-increment loop-condition safety invariant.

## Retry Iteration 7: regenerated goals after conditional-bound invariant

After replacing the invariant with the conditional source-level bound:

```c
1 <= i && i <= n + 1 &&
(1 < n => i + 1 <= n) &&
...
```

and removing the pre-loop assertion that demanded `n <= INT_MAX`, `symexec` succeeded again. The current `coq/generated/array_first_peak_proof_manual.v` now contains only two manual placeholders:

```coq
Lemma proof_of_array_first_peak_entail_wit_3 : array_first_peak_entail_wit_3.
Proof. Admitted.

Lemma proof_of_array_first_peak_return_wit_2 : array_first_peak_return_wit_2.
Proof. Admitted.
```

The previous unprovable `array_first_peak_entail_wit_1` no longer appears in the manual file. Its regenerated goal in `array_first_peak_goal.v` only asks for initialization of:

```coq
[| (1 <= 1) |] &&
[| (1 <= n_pre + 1) |] &&
[| (1 < n_pre -> 1 + 1 <= n_pre) |] &&
...
```

which is auto-solvable from `0 <= n_pre`. The `INT_MAX` safety witnesses remain in `goal.v`, for example `array_first_peak_safety_wit_2` requires `i + 1 <= INT_MAX`, but those witnesses include stack cells:

```coq
((&("i"))) # Int |-> i **
((&("n"))) # Int |-> n_pre **
((&("a"))) # Ptr |-> a_pre **
IntArray.full a_pre n_pre l
```

so they can be handled by the generated/auto side using the local integer range of `n`, as in the `array_count_increasing_steps` example.

The remaining manual theorem `array_first_peak_entail_wit_3` is only the loop-exit bridge:

```coq
Hexit : i + 1 >= n_pre
Hprefix : forall j_2, 0 < j_2 /\ j_2 < i -> not_peak j_2
|--
forall j, 0 < j /\ j + 1 < n_pre -> not_peak j
```

The proof is arithmetic: from `j + 1 < n_pre` and `i + 1 >= n_pre`, derive `j < i`, then apply the prefix hypothesis. To avoid fragile generated hypothesis names, select the prefix hypothesis by its type:

```coq
match goal with
| Hprefix : forall k : Z, 0 < k /\ k < i -> _ |- _ =>
    apply Hprefix
end.
lia.
```

The remaining `array_first_peak_return_wit_2` is the concrete `return -1` disjunction. After `pre_process; entailer!`, choose the right disjunct and let `entailer!` discharge `-1 = -1`, the quantified no-peak fact, and the preserved `IntArray.full`.
