# Issues

## Fingerprint initialization

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and `{}` keywords.
- Trigger: workspace bootstrap left task-specific retrieval metadata blank.
- Localization: `output/verify_20260422_220436_selection_sort/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled a non-empty semantic description for in-place selection sort and controlled-vocabulary keywords only:

```json
"algorithm_family": "selection",
"control_flow": ["for_loop", "nested_loop", "if"],
"data_shape": ["array", "pointer"],
"semantic_intent": "in_place_update",
"proof_pattern": ["loop_invariant", "case_split", "range_bound", "heap_reasoning"]
```

- Result: the fingerprint is no longer empty and now records final verification statuses `goal_check_passed`, `proof_check_passed`, `manual_witness_needed`, `auto_proof_contains_admitted`, and `generated_goal_contains_axioms`.

## Missing loop invariants

- Phenomenon: the baseline symexec run on the unannotated active file failed before usable VC generation. `logs/qcp_run.log` reported:

```text
fatal error: Error: Lack of assertions in some paths for the loop! in annotated/verify_20260422_220436_selection_sort.c:30:8
```

- Trigger: the active annotated C had nested loops with no `Inv`. The relevant C fragment was:

```c
for (i = 0; i < n; ++i) {
    min_idx = i;
    for (j = i + 1; j < n; ++j) {
        if (a[j] < a[min_idx]) {
            min_idx = j;
        }
    }
    tmp = a[i];
    a[i] = a[min_idx];
    a[min_idx] = tmp;
}
```

- Localization: `annotated/verify_20260422_220436_selection_sort.c`, outer loop and inner loop.
- Fix: added an outer invariant carrying current array list `l_outer`, length `Zlength(l_outer) == n@pre`, `Permutation(l, l_outer)`, pairwise sorted processed prefix, prefix-to-suffix ordering, parameter equalities `n == n@pre` and `a == a@pre`, and `IntArray::full(a, n@pre, l_outer)`. Added an inner invariant carrying current list `l_inner`, scan bounds, `i <= min_idx < j`, the same outer semantic facts, and a minimum fact:

```c
(forall (k: Z),
  (i <= k && k < j) =>
  l_inner[min_idx] <= l_inner[k])
```

- Result: after clearing stale generated files and rerunning symexec with `--coq-logic-path=SimpleC.EE.CAV.verify_20260422_220436_selection_sort`, symbolic execution succeeded and generated fresh `selection_sort_goal.v`, `selection_sort_proof_auto.v`, `selection_sort_proof_manual.v`, and `selection_sort_goal_check.v`.

## Manual proof for non-adjacent selection-sort swap

- Phenomenon: fresh `selection_sort_proof_manual.v` contained four generated `Admitted.` obligations:

```coq
proof_of_selection_sort_entail_wit_1
proof_of_selection_sort_entail_wit_2
proof_of_selection_sort_entail_wit_4
proof_of_selection_sort_return_wit_1
```

- Trigger: the outer-loop preservation witness after the final swap must prove that a non-adjacent two-index swap preserves length, preserves `Permutation`, extends pairwise prefix ordering from `i` to `i + 1`, preserves prefix-to-suffix ordering, and converts local stores for `j`, `min_idx`, and `tmp` to undef stores.
- Localization: `output/verify_20260422_220436_selection_sort/coq/generated/selection_sort_proof_manual.v`, theorem `proof_of_selection_sort_entail_wit_4`.
- Fix: added local helper lemmas for `replace_nth` length and lookup behavior, `replace_Znth` length and lookup behavior, `selection_sort_swap`, swap length, swap `Znth` at `i`, at `min_idx`, and at unrelated positions, non-adjacent swap permutation via a prefix/mid/tail split, pairwise-prefix preservation, and cross-order preservation. The main witness uses:

```coq
Exists (selection_sort_swap l_inner i min_idx).
...
eapply selection_sort_swap_cross_order with (n := n_pre).
eapply selection_sort_swap_pairwise_prefix with (n := n_pre).
eapply Permutation_trans with (l' := l_inner).
```

- Result: all four manual obligations are proved. `selection_sort_proof_manual.v` now contains no `Admitted.` and no top-level `Axiom`.

## Proof iteration pitfalls

- Phenomenon: early versions of the manual proof failed in several stable ways:
  - pairwise helper branch `p = q = i` failed because only one side of `Znth i (selection_sort_swap ...)` was rewritten;
  - `entailer!` reordered remaining goals, so a permutation proof was attempted while the active goal was an ordering fact;
  - generated chained comparisons such as `0 <= p <= q /\ q < i` did not directly match helper preconditions shaped as flatter conjunctions;
  - bare `eapply Permutation_trans` left an existential middle list and a later `Zlength` subgoal.
- Trigger: the current contract uses pairwise sortedness directly instead of the older archived `sorted_z` predicate, so the archived selection-sort proof pattern needed adaptation rather than direct copying.
- Localization: `selection_sort_proof_manual.v`, helper `selection_sort_swap_pairwise_prefix` and theorem `proof_of_selection_sort_entail_wit_4`.
- Fixes:
  - rewrote both sides with `selection_sort_swap_Znth_i` in the `p = q = i` branch;
  - reordered `entail_wit_4` bullets to handle local-store cleanup, cross order, pairwise prefix, permutation, then length;
  - replaced direct `exact` uses of generated range hypotheses with `apply H...; lia`;
  - pinned the transitivity middle list using `eapply Permutation_trans with (l' := l_inner)`.
- Result: the final compile replay passed `selection_sort_goal.v`, `selection_sort_proof_auto.v`, `selection_sort_proof_manual.v`, and `selection_sort_goal_check.v`.

## Final compile and cleanup

- Phenomenon: Coq compilation produced `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` byproducts under `output/verify_20260422_220436_selection_sort/coq/generated/`.
- Trigger: standard `coqc` compile replay of generated files.
- Localization: `output/verify_20260422_220436_selection_sort/coq/generated/`.
- Fix: removed all non-`.v` files under the workspace `coq/` tree after successful `goal_check` compilation. Also checked `input/` for non-`.c`/non-`.v` byproducts; none were present.
- Result: cleanup check found no non-`.v` files under `output/verify_20260422_220436_selection_sort/coq/`, and no non-`.c`/non-`.v` files under `input/`.
