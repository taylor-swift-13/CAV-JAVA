# Verify Issues: array_reverse_in_place

## 2026-04-22 07:44 +0800 - Fingerprint placeholder filled before verification

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and `{}` keywords.
- Trigger: the verify workflow requires this file to be populated early, with keyword keys and values drawn only from `doc/retrieval/INDEX.md`.
- Fix: read `doc/retrieval/INDEX.md`, then filled the semantic description for an in-place two-pointer integer-array reverse and used controlled vocabulary values such as `two_pointers`, `while_loop`, `array`, `in_place_update`, `loop_invariant`, `heap_reasoning`, `range_bound`, and `empty_loop_possible`.
- Result: the fingerprint is non-empty and was later updated with `verification_status: goal_check_passed` after successful compile.

## 2026-04-22 07:45 +0800 - Missing loop invariant for in-place array reverse

- Phenomenon: the input function had a mutating `while (left < right)` loop with no `Inv`, so the verifier had no persistent description of the evolving `IntArray::full(a, n, ...)` heap list.
- Trigger: final postcondition requires `IntArray::full(a, n, rev(l))`, while the loop swaps symmetric endpoints and changes the array contents each iteration.
- Fix: added an invariant before the loop in `annotated/verify_20260422_074343_array_reverse_in_place.c` describing the current list as:

```c
IntArray::full(a, n@pre,
  app(rev(sublist(n@pre - left, n@pre, l)),
    app(sublist(left, right + 1, l),
      rev(sublist(0, left, l)))))
```

  plus bounds and unchanged parameter facts (`n == n@pre`, `a == a@pre`, `right == n@pre - 1 - left`).
- Result: `symexec` generated fresh `array_reverse_in_place_goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.

## 2026-04-22 07:50 +0800 - Exit invariant was too weak without crossing bound

- Phenomenon: proof analysis of `array_reverse_in_place_return_wit_1` showed that `left >= right` and `right == n@pre - 1 - left` alone did not force the unprocessed middle segment to have length zero or one.
- Trigger: the invariant admitted unreachable arithmetic states, for example `n = 5, left = 4, right = 0`, which satisfy the equation and exit guard but cannot arise from the loop and do not make the invariant list reduce to `rev(l)`.
- Fix: strengthened the loop invariant with:

```c
left <= right + 1
```

  This is initialized from `0 <= n`, preserved because the loop body runs only under `left < right`, and at exit combines with `left >= right` to give the two real crossing cases.
- Result: reran `symexec` as required; the regenerated goals included the new pure fact in preservation and return witnesses.

## 2026-04-22 07:47-08:04 +0800 - Manual proof required list decomposition helpers

- Phenomenon: the regenerated `proof_manual.v` contained three admitted lemmas: invariant initialization, loop-step preservation, and return witness.
- Trigger: `entailer!` could not close heap predicates whose list arguments differed by pure list equalities involving `sublist`, `rev`, and a double `replace_Znth` swap.
- Fixes:
  - For `entail_wit_1`, normalized `sublist(n_pre, n_pre, l)`, `sublist(0, n_pre, l)`, `sublist(0, 0, l)`, and `l ++ nil`.
  - Added `replace_Znth_boundary_swap` for the generic update shape `p ++ x :: mid ++ y :: s`.
  - Added `reverse_step_current_decomp` and `reverse_step_target_decomp` to align the generated double-write list with the next loop invariant.
  - Added `reverse_exit_decomp` to split exit into `left = right` and `left = right + 1`, then rebuild `rev(l)` from prefix/middle/suffix sublists.
- Representative proof fragment:

```coq
replace (replace_Znth right x (replace_Znth left y (p ++ x :: mid ++ y :: s)))
  with (p ++ y :: mid ++ x :: s).
2: {
  replace left with (Zlength p) by lia.
  replace right with (Zlength p + 1 + Zlength mid) by lia.
  symmetry.
  apply replace_Znth_boundary_swap.
}
rewrite Htarget.
entailer!.
```

- Result: `coq/generated/array_reverse_in_place_proof_manual.v` compiles and contains no `Admitted.` or new `Axiom`.

## 2026-04-22 07:47 +0800 - Compile replay initially hid a failed proof

- Phenomenon: an early compile replay log showed a `proof_manual.v` error and then a later `goal_check.v` path error, while the shell command itself returned success.
- Trigger: the redirected command block did not use fail-fast behavior, so later `coqc` commands ran after an earlier `coqc` failure.
- Fix: changed compile replay blocks to include `set -e` inside the redirected command group.
- Result: subsequent compile attempts stopped at the first real Coq failure, and the final fail-fast replay compiled `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` successfully.

## 2026-04-22 08:04 +0800 - Coq intermediate files cleaned

- Phenomenon: successful Coq compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Trigger: workflow completion requires cleaning non-`.v` intermediates from the workspace `coq/` tree.
- Fix: ran `find .../coq -type f ! -name '*.v' -delete`.
- Result: `find .../coq -type f ! -name '*.v'` returned no files.
