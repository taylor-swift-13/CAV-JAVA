# Annotation Reasoning

## Iteration 1: add scan invariant and loop-exit bridge

Current annotated file is identical to the input contract and has no loop annotation:

```c
int i = 1;

while (i + 1 < n) {
    if (a[i] >= a[i - 1] && a[i] >= a[i + 1]) {
        return i;
    }
    i++;
}

return -1;
```

The loop scans interior indices from left to right. At the loop-head control point, `i` is the next candidate index to check, so the durable semantic fact must be about the already checked prefix: every interior index `j` with `0 < j && j < i` is not a peak, i.e. `l[j] < l[j - 1] || l[j] < l[j + 1]`. This is exactly the prefix fact needed by the successful return branch, because returning at current `i` requires the postcondition's prefix fact for all `0 < j && j < __return`.

The invariant also needs to preserve unchanged parameters and heap ownership:

```c
/*@ Inv
      1 <= i && i <= n + 1 &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z),
        (0 < j && j < i) =>
        (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
      IntArray::full(a, n, l)
*/
while (i + 1 < n) { ... }
```

Initialization holds because `i == 1`, `0 <= n` from the precondition gives `1 <= n + 1`, and the quantified prefix `0 < j && j < 1` is empty. Preservation holds because the only path that continues past the `if` is the path where the current index is not a peak. The failed condition `!(a[i] >= a[i - 1] && a[i] >= a[i + 1])`, together with the array values from `IntArray::full(a, n, l)`, gives `l[i] < l[i - 1] || l[i] < l[i + 1]`; after `i++`, the checked prefix extends from `j < i` to `j < i + 1`.

At loop exit, the postcondition for returning `-1` quantifies `0 < j && j + 1 < n`, not `j < i`. Since the loop exits with `!(i + 1 < n)`, we have `n <= i + 1`; from `j + 1 < n` it follows that `j < i`. A small exit assertion will make that range conversion explicit before local variable cleanup:

```c
/*@ Assert
      i + 1 >= n &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z),
        (0 < j && j + 1 < n) =>
        (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
      IntArray::full(a, n, l)
*/
return -1;
```

This assertion is placed immediately after the loop and before `return -1`, matching the control-point guidance: it only bridges the loop invariant range to the final return witness range and keeps the heap predicate available for the postcondition.

## Iteration 2: strengthen invariant for `i + 1` safety

The first Coq compile attempt after successful `symexec` failed in `proof_of_array_first_peak_safety_wit_2`:

```text
File ".../array_first_peak_proof_manual.v", line 25, characters 2-5:
Error: Tactic failure: Cannot find witness.
```

Inspecting the proof state with `coqtop` showed the remaining goal was:

```coq
H  : 1 <= i
H0 : i <= n_pre + 1
H2 : 0 <= n_pre
H3 : Zlength l = n_pre
============================
i + 1 <= 2147483647
```

This is not a proof-script issue. The invariant allowed the unreachable but syntactically possible state `i = n + 1`, which is too weak for proving the next loop-condition evaluation `i + 1 < n` is C-int-safe. The actual program state is stronger: initially `i == 1`, and after a continuing loop body the old condition `i + 1 < n` ensures the incremented index is still below `n`. To expose the needed safety facts to `symexec`, the invariant should explicitly preserve:

```c
n <= INT_MAX &&
i + 1 <= INT_MAX
```

`n <= INT_MAX` is available from the C `int` parameter representation and is needed to preserve `i + 1 <= INT_MAX` after `i++`: old `i + 1 < n` implies new `i + 1 <= n`, hence new `i + 1 <= INT_MAX`. The exit assertion also keeps `n <= INT_MAX`; the final postcondition does not need it semantically, but it remains a harmless pure fact before returning.

## Retry Iteration 3: remove uninitializable `n <= INT_MAX` from the invariant

Batch Coq replay and a fresh `coqtop` probe in this retry showed that the strengthened invariant from iteration 2 is too strong at the loop-initialization control point. The current generated witness is:

```coq
Definition array_first_peak_entail_wit_1 :=
forall (a_pre: Z) (n_pre: Z) (l: list Z),
  [| 0 <= n_pre |] &&
  [| Zlength l = n_pre |] &&
  IntArray.full a_pre n_pre l
|--
  [| 1 <= 1 |] &&
  [| 1 <= n_pre + 1 |] &&
  [| n_pre <= INT_MAX |] &&
  [| 1 + 1 <= INT_MAX |] && ...
```

After `pre_process`, `logs/coqtop_retry_entail_wit_1.log` leaves:

```coq
a_pre, n_pre : Z
l : list Z
H  : 0 <= n_pre
H0 : Zlength l = n_pre
============================
IntArray.full a_pre n_pre l
|-- [| n_pre <= 2147483647 |] && ...
```

This proves that `n <= INT_MAX` is not available from the formal input contract at this pure assertion point. However, the loop-condition safety fact that first motivated the strengthening was specifically `i + 1 <= INT_MAX`, not a semantic postcondition requirement about `n`. The invariant can keep the narrower directly needed safety fact:

```c
1 <= i && i <= n + 1 &&
i + 1 <= INT_MAX &&
...
```

Initialization of `i + 1 <= INT_MAX` holds because `i == 1`, so it reduces to `2 <= INT_MAX`, independent of the input length. The exit assertion also does not need `n <= INT_MAX` for the return `-1` postcondition; it only needs the loop-exit bridge:

```c
i + 1 >= n &&
(forall (j: Z),
  (0 < j && j + 1 < n) =>
  (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
IntArray::full(a, n, l)
```

Planned annotation edit: remove only the pure `n <= INT_MAX &&` conjunct from the loop invariant and from the loop-exit assertion, while preserving the processed-prefix semantic invariant, `i + 1 <= INT_MAX`, unchanged parameters, and `IntArray::full(a, n, l)`. Then clear and regenerate the Coq files with `symexec`. If preservation of `i + 1 <= INT_MAX` still requires a hidden upper bound on `n`, that will appear in the regenerated `entail_wit_2_*` proof state rather than blocking invariant initialization.

## Retry Iteration 4: add a pre-loop bridge assertion for C-int range of `n`

The narrowed invariant removed the initialization blocker, and `symexec` regenerated preservation witnesses. Batch compilation then exposed the expected preservation arithmetic blocker in `proof_of_array_first_peak_entail_wit_2_1`: after the loop body increments `i`, the invariant must prove `((i + 1) + 1) <= INT_MAX` for the next loop-condition evaluation. The live state in `logs/coqtop_retry_entail_2_1_current.log` after `entailer!` included:

```coq
H0 : i + 1 < n_pre
H3 : i + 1 <= 2147483647
...
============================
i + 1 + 1 <= 2147483647
```

This cannot follow from `i + 1 < n_pre` unless the verifier also has `n_pre <= INT_MAX`. The previous attempt put `n <= INT_MAX` directly in the loop invariant, but invariant initialization was generated from the pure precondition:

```coq
0 <= n_pre
Zlength l = n_pre
IntArray.full a_pre n_pre l
```

and therefore could not prove `n_pre <= INT_MAX`.

The missing fact is nevertheless available at the program point immediately after `int i = 1;`, because `n` is a C `int` parameter stored in the local variable state. The fix is a Verify-level bridge assertion before the loop, at a point where the local `n` value is still present, which records the initialized loop invariant including `n <= INT_MAX`:

```c
/*@ Assert
      1 <= i && i <= n + 1 &&
      n <= INT_MAX &&
      i + 1 <= INT_MAX &&
      a == a@pre &&
      n == n@pre &&
      (forall (j: Z),
        (0 < j && j < i) =>
        (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
      IntArray::full(a, n, l)
*/
```

This assertion is not a contract change. It only materializes the C-int range fact from the current local variable representation before the loop invariant consumes it. The loop invariant and loop-exit assertion should again include `n <= INT_MAX`: the invariant needs it to preserve `i + 1 <= INT_MAX` across `i++`, and the exit assertion may carry it harmlessly as a pure fact while bridging to the `-1` return postcondition.

## Retry 2026-04-22 04:41:54 +0800: avoid uninitializable `n <= INT_MAX` invariant by using a conditional loop bound

The pre-loop bridge assertion from Retry Iteration 4 did not materialize the C-int range fact for `n`. The regenerated VC `output/verify_20260422_042345_array_first_peak/coq/generated/array_first_peak_goal.v` still defines `array_first_peak_entail_wit_1` with only:

```coq
[| 0 <= n_pre |] &&
[| Zlength l = n_pre |] &&
IntArray.full a_pre n_pre l
```

on the left and:

```coq
[| n_pre <= INT_MAX |] &&
[| 1 + 1 <= INT_MAX |] && ...
```

on the right. Batch replay in `logs/compile_retry2_20260422.log` again fails in `proof_of_array_first_peak_entail_wit_1`, so the bridge assertion is not a viable repair.

A closer annotation pattern exists in `examples/array_count_increasing_steps/annotated/array_count_increasing_steps.c`, which also uses the guard `i + 1 < n` without putting `n <= INT_MAX` in the invariant. That example keeps a source-level conditional bound:

```c
(0 < n => i + 1 <= n)
```

and its manual proof later derives concrete `INT_MAX` safety from the live stack cell for `n` in safety witnesses using:

```coq
prop_apply (store_int_range (&("n")) n_pre).
```

For `array_first_peak`, initialization starts with `i == 1`, and the contract allows `n == 0` and `n == 1`. Therefore the conditional bound must be guarded by `1 < n`, not just `0 < n`:

```c
1 <= i && i <= n + 1 &&
(1 < n => i + 1 <= n) &&
a == a@pre &&
n == n@pre &&
(forall (j: Z),
  (0 < j && j < i) =>
  (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
IntArray::full(a, n, l)
```

Initialization: `1 <= i` and `i <= n + 1` follow from `i == 1` and `0 <= n`; if `1 < n`, then `i + 1 <= n` is `2 <= n`; the prefix fact is vacuous for `0 < j && j < 1`.

Preservation: the guard gives old `i + 1 < n`; after `i++`, new `i` is old `i + 1`, and for `1 < n` the new conditional bound requires old `i + 2 <= n`, which follows from old `i + 1 < n`. The no-return branch supplies either `l[i] < l[i - 1]` or `l[i] < l[i + 1]`, extending the prefix from `j < i` to `j < i + 1`.

Exit: with loop exit `i + 1 >= n`, any postcondition index satisfying `0 < j && j + 1 < n` also satisfies `j < i`, so the invariant prefix fact proves the `-1` return case.

Planned edit: remove the pre-loop assertion that demands `n <= INT_MAX`; replace the loop invariant with the conditional-bound shape above; remove `n <= INT_MAX` from the loop-exit assertion. Then rerun `symexec` before editing generated proofs.
