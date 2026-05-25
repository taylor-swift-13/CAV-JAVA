# Proof reasoning

## 2026-04-22 manual entailment witnesses for `array_find_last_equal`

After successful `symexec`, `output/verify_20260422_040059_array_find_last_equal/coq/generated/array_find_last_equal_proof_manual.v` contains four admitted manual lemmas:

```coq
Lemma proof_of_array_find_last_equal_entail_wit_1 : array_find_last_equal_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_find_last_equal_entail_wit_2_1 : array_find_last_equal_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_find_last_equal_entail_wit_3 : array_find_last_equal_entail_wit_3.
Proof. Admitted.

Lemma proof_of_array_find_last_equal_return_wit_1 : array_find_last_equal_return_wit_1.
Proof. Admitted.
```

The corresponding goals in `array_find_last_equal_goal.v` are pure assertion entailments:

- `array_find_last_equal_entail_wit_1`: initialize the invariant after `ans = -1` and `i = 0`. The only semantic fact is the vacuous universal over `0 <= j < 0`; arithmetic and the array resource are unchanged.
- `array_find_last_equal_entail_wit_2_1`: preserve the invariant in the branch where `Znth i l 0 = k_pre` and the C code assigns `ans = i`. The new nonnegative implication follows from the branch equality, and its suffix universal is vacuous because `i < j < i + 1` is impossible.
- `array_find_last_equal_entail_wit_3`: after loop exit, `i >= n_pre` and `i <= n_pre` imply `i = n_pre`; the implications over `[0, i)` can be reused over `[0, n_pre)`.
- `array_find_last_equal_return_wit_1`: final postcondition is an assertion-level disjunction. From `-1 <= ans`, either `ans = -1`, in which case choose the no-match right branch, or `ans <> -1`, which implies `0 <= ans`, then choose the left branch and use the invariant's nonnegative implication.

First proof attempt will use the standard local pattern from nearby examples:

```coq
unfold <witness>.
intros.
entailer!.
```

For the return witness, the proof must use assertion-level `Left` and `Right`, not lowercase `left` and `right`, because the goal is `P |-- Q1 || Q2` in the separation-logic assertion language.

## 2026-04-22 compile failure: `entail_wit_1` solved by `entailer!`

First compile attempt reached `array_find_last_equal_proof_manual.v` and failed at line 26:

```text
File ".../array_find_last_equal_proof_manual.v", line 26, characters 2-14:
Error: No such goal.
```

The failing proof fragment was:

```coq
Lemma proof_of_array_find_last_equal_entail_wit_1 : array_find_last_equal_entail_wit_1.
Proof.
  unfold array_find_last_equal_entail_wit_1.
  intros.
  entailer!.
  intros j Hj.
  lia.
Qed.
```

This means `entailer!` already discharged the vacuous initialization implication and all pure/resource goals. The extra `intros j Hj` was running after all goals were closed. The next edit removes the dead lines and leaves `entail_wit_1` as the minimal stable script:

```coq
unfold array_find_last_equal_entail_wit_1.
intros.
entailer!.
```

## 2026-04-22 compile failure: `entail_wit_2_1` also solved by `entailer!`

Second compile attempt failed at line 33 with:

```text
Error: [Focus] Wrong bullet -: No more goals.
```

The proof fragment was:

```coq
unfold array_find_last_equal_entail_wit_2_1.
intros.
entailer!.
- intros Hi_eq.
  lia.
- intros Hi_nonneg.
  split; [assumption |].
  intros j Hj.
  lia.
```

The line-33 bullet was the first bullet after `entailer!`, so `entailer!` had already solved both implication goals: the `i = -1` guard is contradictory under `0 <= i`, and the `0 <= i` branch follows directly from the branch equality plus the impossible interval `i < j < i + 1`. The next edit removes the unused bullets and keeps the minimal proof.

## 2026-04-22 proof-state inspection for `entail_wit_3`

Third compile attempt failed at line 40:

```text
Error: Tactic failure: Cannot find witness.
```

The failing script was:

```coq
unfold array_find_last_equal_entail_wit_3.
intros.
entailer!.
- lia.
- intros Hans.
  subst i.
  auto.
- intros Hans_nonneg.
  subst i.
  auto.
```

`coqtop` after `entailer!. Show.` revealed that the remaining goals are not the arithmetic equality first; `entailer!` has already consumed the arithmetic parts and leaves the two semantic implication goals:

```coq
H  : i >= n_pre
H1 : i <= n_pre
H6 : ans = -1 -> forall j_3, 0 <= j_3 < i -> Znth j_3 l 0 <> k_pre
H7 : 0 <= ans -> Znth ans l 0 = k_pre /\
                  forall j_4, ans < j_4 < i -> Znth j_4 l 0 <> k_pre
|-- 0 <= ans -> Znth ans l 0 = k_pre /\
                 forall j_2, ans < j_2 < n_pre -> Znth j_2 l 0 <> k_pre
```

and then:

```coq
|-- ans = -1 -> forall j, 0 <= j < n_pre -> Znth j l 0 <> k_pre
```

The needed bridge is the exit equality `i = n_pre`, derived from `i >= n_pre` and `i <= n_pre`. The next proof explicitly asserts that equality before `entailer!`, then proves each implication by applying `H7` or `H6` and rewriting the bound with `lia`.

Follow-up compile result: asserting `i = n_pre` before `entailer!` failed with `Cannot find witness` because the pure facts are still inside the separation-logic assertion, not Coq hypotheses, until `entailer!` introduces them. The equality assertion must be inside each remaining subgoal after `entailer!`, where the context contains:

```coq
H  : i >= n_pre
H1 : i <= n_pre
```

The proof is adjusted accordingly.

Follow-up parser failure: under `Local Open Scope sac`, Coq reported a syntax error at compact tactic syntax:

```coq
split; [exact Hans_val |].
```

The fix is purely syntactic: use ordinary bullets after `split` instead of the bracketed branch form.

## 2026-04-22 proof-state inspection for `return_wit_1`

Compile then failed in `return_wit_1` at the line:

```coq
assert (Hans_nonneg : 0 <= ans) by lia.
```

This happened before the assertion hypotheses had been extracted. `coqtop` with:

```coq
unfold array_find_last_equal_return_wit_1.
pre_process.
Show.
```

gave the usable context:

```coq
H0 : -1 <= ans
H1 : ans < n_pre
H3 : ans = -1 -> forall j, 0 <= j < n_pre -> Znth j l 0 <> k_pre
H4 : 0 <= ans -> Znth ans l 0 = k_pre /\
                  forall j_2, ans < j_2 < n_pre -> Znth j_2 l 0 <> k_pre
|-- IntArray.full a_pre n_pre l |-- positive_case || negative_case
```

The return proof should therefore start with `pre_process`, then split on `Z.eq_dec ans (-1)`. In the equality case, choose assertion-level `Right` and use `H3`; in the non-equality case, derive `0 <= ans` from `H0` and choose assertion-level `Left`, using `H4`.
