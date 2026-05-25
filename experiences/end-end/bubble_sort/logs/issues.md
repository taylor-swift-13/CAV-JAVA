## 2026-04-22 13:01 +0800 - Fingerprint initially had empty semantic metadata

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and empty `keywords`:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger condition: verify workflow requires this metadata to be filled early, after reading `doc/retrieval/INDEX.md`, using only controlled vocabulary keys and values.
- Localization: `output/verify_20260422_130100_bubble_sort/logs/workspace_fingerprint.json`.
- Fix action: described `bubble_sort` as an in-place nested-loop adjacent-swap array sort preserving permutation and producing sorted output. Filled controlled keywords: `selection`, `for_loop`, `nested_loop`, `array`, `in_place_update`, `loop_invariant`, `heap_reasoning`, `case_split`, `int_range`, `overflow_guard`, and `empty_loop_possible`.
- Result: the fingerprint is usable for retrieval and was extended after final verification with `goal_check_passed`, `proof_check_passed`, `auto_proof_contains_admitted`, and `generated_goal_contains_axioms`.

## 2026-04-22 13:02 +0800 - Active annotated C initially had no nested-loop invariants

- Phenomenon: the active annotated file matched `input/bubble_sort.c` and had no invariant before either loop:

```c
for (i = 0; i < n; ++i) {
    for (j = 0; j + 1 < n - i; ++j) {
        if (a[j] > a[j + 1]) {
            int t = a[j];
            a[j] = a[j + 1];
            a[j + 1] = t;
        }
    }
}
```

- Trigger condition: the function mutates `IntArray::full(a, n, l)` by adjacent swaps, while the postcondition requires both sortedness and `Permutation(l, l0)`. Without invariants, symbolic execution has no current ghost list, no sorted suffix state, and no local maximum fact for the bubble pass.
- Localization: `annotated/verify_20260422_130100_bubble_sort.c`, immediately before the outer and inner `for` loops.
- Fix action: added an outer invariant carrying `exists lc`, bounds for `i`, stable `n` and `a`, `Zlength(lc) == n@pre`, `Permutation(l, lc)`, a sorted suffix `[n@pre - i, n@pre)`, prefix-to-suffix ordering, and `IntArray::full(a, n@pre, lc)`. Added an inner invariant carrying the same global facts plus `0 <= j && j + 1 <= n@pre - i` and the local maximum fact:

```c
(forall (p: Z), (0 <= p && p < j) => lc[p] <= lc[j])
```

- Result: after clearing generated files and rerunning `symexec`, symbolic execution completed successfully and generated fresh `bubble_sort_goal.v`, `bubble_sort_proof_auto.v`, `bubble_sort_proof_manual.v`, and `bubble_sort_goal_check.v`.

## 2026-04-22 13:03 +0800 - Manual proof required adjacent-swap helper lemmas

- Phenomenon: `bubble_sort_proof_manual.v` initially contained five admitted manual obligations:

```coq
proof_of_bubble_sort_entail_wit_1
proof_of_bubble_sort_entail_wit_2
proof_of_bubble_sort_entail_wit_3_1
proof_of_bubble_sort_entail_wit_4
proof_of_bubble_sort_return_wit_1
```

- Trigger condition: `entail_wit_3_1` contains the swap-branch heap list:

```coq
replace_Znth (j + 1) (Znth j lc_3 0)
  (replace_Znth j (Znth (j + 1) lc_3 0) lc_3)
```

The proof needs length, point-lookup, permutation, suffix-order, cross-order, and local-maximum preservation facts for this adjacent swap.
- Localization: `output/verify_20260422_130100_bubble_sort/coq/generated/bubble_sort_proof_manual.v`.
- Fix action: added local helper lemmas for `replace_nth`, `replace_Znth`, `bubble_sort_adjacent_swap`, adjacent-swap permutation, inner-loop order preservation, and outer suffix extension. Replaced all five `Admitted.` bodies with explicit proofs.
- Result: `bubble_sort_proof_manual.v` compiles and contains no `Admitted.` or added `Axiom`.

## 2026-04-22 13:04 +0800 - Helper proof shadowed an index variable

- Phenomenon: the first compile replay failed with:

```text
File ".../bubble_sort_proof_manual.v", line 54, characters 4-14:
Error: Not an inductive definition.
```

- Trigger condition: `bubble_sort_nth_replace_nth_other` used `induction l; intros; destruct a`, but after induction the list head binder shadowed the natural index parameter `a`.
- Localization: local helper `bubble_sort_nth_replace_nth_other`.
- Fix action: rewrote the helper proof to introduce index names before induction:

```coq
intros T l idx repl v u Hneq.
revert idx repl Hneq.
induction l; intros idx repl Hneq.
```

- Result: the helper compiled and later `replace_Znth` lookup lemmas could use it.

## 2026-04-22 13:08 +0800 - Outer-loop preservation had a local-variable cleanup entailment before pure goals

- Phenomenon: `proof_of_bubble_sort_entail_wit_4` first failed with `No product even after head-reduction` when the script tried `intros p q Hpq` on the first remaining goal after `entailer!`.
- Trigger condition: the first remaining goal was separation logic cleanup for local `j`, not a quantified pure order goal:

```coq
&( "j") # Int |-> j |-- &( "j") # Int |->_
```

- Localization: `proof_of_bubble_sort_entail_wit_4`.
- Fix action: handled the local variable entailment first:

```coq
sep_apply store_int_undef_store_int.
entailer!.
```

Then proved the remaining cross-order and suffix-order goals using `bubble_sort_outer_cross_extend` and `bubble_sort_outer_suffix_extend`.
- Result: outer-loop preservation compiled.

## 2026-04-22 13:15 +0800 - Final compile and cleanup

- Phenomenon: verify completion requires more than a successful manual proof; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must all compile, and non-`.v` Coq intermediates must be removed.
- Trigger condition: after successful `coqc`, the workspace contained `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under `coq/generated/`.
- Fix action: ran the documented compile sequence from `QualifiedCProgramming/SeparationLogic`, confirmed `goal_check.v` passed, checked `bubble_sort_proof_manual.v` for `Admitted.` and top-level `Axiom`, then deleted all non-`.v` files under `output/verify_20260422_130100_bubble_sort/coq/`.
- Result: final workspace `coq/` contains only generated `.v` sources; `input/` had no non-`.c`/`.v` intermediates to clean.
