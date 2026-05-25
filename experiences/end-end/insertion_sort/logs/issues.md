## 2026-04-22 17:43 +0800 - Fingerprint initially had empty semantic metadata

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger condition: the verify workflow requires this metadata to be filled early, after reading `doc/retrieval/INDEX.md`, and `keywords` must use only controlled vocabulary keys and values.
- Localization: `output/verify_20260422_174132_insertion_sort/logs/workspace_fingerprint.json`.
- Fix action: described `insertion_sort` as an in-place nested-loop integer-array insertion sort with an outer processed-prefix loop and an inner shifted-hole loop. Filled controlled keywords including `greedy`, `for_loop`, `while_loop`, `nested_loop`, `array`, `pointer`, `in_place_update`, `loop_invariant`, `heap_reasoning`, `case_split`, `range_bound`, `int_range`, `overflow_guard`, and `empty_loop_possible`.
- Result: the fingerprint is non-empty and now also records final controlled verification-status values including `goal_check_passed`, `manual_witness_needed`, `auto_proof_contains_admitted`, and `generated_goal_contains_axioms`.

## 2026-04-22 17:44 +0800 - Active annotated C initially had no insertion-sort invariants

- Phenomenon: the active annotated file initially had no `Inv` before either loop:

```c
for (i = 1; i < n; ++i) {
    key = a[i];
    j = i - 1;
    while (j >= 0 && a[j] > key) {
        a[j + 1] = a[j];
        j--;
    }
    a[j + 1] = key;
}
```

- Trigger condition: the function mutates `IntArray::full(a, n, l)`, while the postcondition needs `insertion_sort_spec(l, lr)` and final array ownership. Without invariants, symbolic execution has no current ghost list, no permutation fact, no sorted-prefix representation, and no way to describe the temporary shifted-hole array state during the inner loop.
- Localization: `annotated/verify_20260422_174132_insertion_sort.c`, immediately before the outer `for` and inner `while`.
- Fix action: added an outer invariant with `exists l_outer`, widened skip-loop-safe bounds `1 <= i && i <= n@pre + 1`, the conditional nonempty bound `(n@pre > 0 => i <= n@pre)`, unchanged `n`/`a`, `Zlength(l_outer) == n@pre`, `Permutation(l, l_outer)`, adjacent order on `[0, i)`, and `IntArray::full(a, n@pre, l_outer)`. Added an inner invariant with `exists l_cur l_base`, key/base relation `key == l_base[i]`, shifted-hole list shape:

```c
l_cur == app(sublist(0, j + 2, l_base),
             app(sublist(j + 1, i, l_base),
                 sublist(i + 1, n@pre, l_base)))
```

plus base length, permutation, adjacent prefix order, and the fact that shifted elements are greater than `key`.
- Result: the annotated C had the semantic state needed for the generated insertion-sort witnesses.

## 2026-04-22 17:44 +0800 - `Permutation` was undeclared in direct C annotations

- Phenomenon: the first `symexec` run failed before VC generation with:

```text
fatal error: Use of undeclared identifier `Permutation' in QCP_examples/CAV/annotated/verify_20260422_174132_insertion_sort.c:37:4
```

- Trigger condition: `input/insertion_sort.v` defines `insertion_sort_spec` using Coq `Permutation`, but the active C invariants mention `Permutation(l, l_outer)` directly. The annotation front end needs a direct `Extern Coq` declaration for any Coq symbol used in C annotations.
- Localization: top of `annotated/verify_20260422_174132_insertion_sort.c`.
- Fix action: added:

```c
/*@ Extern Coq (Permutation: list Z -> list Z -> Prop) */
```

near the existing `Extern Coq insertion_sort_spec` and `Import Coq Require Import insertion_sort` lines.
- Result: rerunning `symexec` after clearing generated files succeeded and generated fresh `insertion_sort_goal.v`, `insertion_sort_proof_auto.v`, `insertion_sort_proof_manual.v`, and `insertion_sort_goal_check.v`.

## 2026-04-22 17:46 +0800 - Manual proof required shifted-hole and final-insertion helper lemmas

- Phenomenon: generated `coq/generated/insertion_sort_proof_manual.v` contained six admitted manual obligations:

```coq
proof_of_insertion_sort_entail_wit_1
proof_of_insertion_sort_entail_wit_2
proof_of_insertion_sort_entail_wit_3
proof_of_insertion_sort_entail_wit_4_1
proof_of_insertion_sort_entail_wit_4_2
proof_of_insertion_sort_return_wit_1
```

- Trigger condition: insertion sort's inner loop is not a simple swap loop. The proof must reason about `replace_Znth (j + 1) (Znth j l_cur 0) l_cur` as one more right-shift of the hole, and about `replace_Znth (j + 1) key l_cur` as the final insertion that restores a normal array list.
- Localization: `output/verify_20260422_174132_insertion_sort/coq/generated/insertion_sort_proof_manual.v`.
- Fix action: added local helper lemmas for `replace_nth`/`replace_Znth` length and lookup, `sublist` full-list normalization, one-step shifted-hole equality, final insertion list shape, final insertion permutation, final insertion length, adjacent-order preservation for the `j >= 0` and `j < 0` branches, and conversion from adjacent order to `StronglySorted Z.le`.
- Result: all six manual obligations were replaced with explicit proofs.

## 2026-04-22 17:49 +0800 - Return proof needed `StronglySorted`, not archived `sorted_z`

- Phenomenon: the current return witness concludes:

```coq
EX lr,
  [| Zlength lr = n_pre |] &&
  [| insertion_sort_spec l lr |] &&
  IntArray.full a_pre n_pre lr
```

and `input/insertion_sort.v` defines:

```coq
Definition insertion_sort_spec (l lr : list Z) : Prop :=
  StronglySorted Z.le lr /\ Permutation l lr.
```

- Trigger condition: an archived proof for an older insertion-sort contract proved a direct `sorted_z` postcondition. Reusing that return proof unchanged would not satisfy this contract.
- Localization: helper and `proof_of_insertion_sort_return_wit_1` in `insertion_sort_proof_manual.v`.
- Fix action: introduced `insertion_sort_adjacent_tail`, `insertion_sort_adjacent_head_forall`, and `insertion_sort_strong_sorted_from_adjacent`. The return proof unfolds `insertion_sort_spec`, proves `StronglySorted Z.le l_outer` from the adjacent-order invariant when `n_pre > 0`, handles the `n_pre == 0` zero-length list case, and reuses the invariant `Permutation l l_outer`.
- Result: the return witness matches the current `insertion_sort_spec` contract.

## 2026-04-22 17:51 +0800 - Helper calls needed current generated hypothesis numbering

- Phenomenon: compile first failed in `entail_wit_3` with:

```text
Error: [Focus] Wrong bullet -: Current bullet - is not finished.
```

Then the final negative branch failed with:

```text
The term "H7" has type "forall k_2 ... adjacent ..."
while it is expected to have type "Permutation l ?l'".
```

- Trigger condition: the current contract includes `Zlength(l) == n@pre`, so `pre_process` generated one extra pure hypothesis compared with the archived proof. Helper calls copied from the archived proof therefore referenced stale `H` numbers for the shifted-hole shape, key equality, and permutation facts.
- Localization: `proof_of_insertion_sort_entail_wit_3` and `proof_of_insertion_sort_entail_wit_4_2` in `insertion_sort_proof_manual.v`.
- Fix action: inspected the current proof state with `coqtop Show`. Updated `entail_wit_3` to use `H10` for the shifted-hole shape and `H9` for the shifted-elements range. Updated the final negative branch to use `H9` for shape, `H4` for key equality, and `H6` for permutation.
- Result: `insertion_sort_proof_manual.v` compiled, and the full compile sequence through `insertion_sort_goal_check.v` passed.

## 2026-04-22 17:52 +0800 - Final compile and cleanup

- Phenomenon: verify completion requires successful compilation of `original/insertion_sort.v`, `insertion_sort_goal.v`, `insertion_sort_proof_auto.v`, `insertion_sort_proof_manual.v`, and `insertion_sort_goal_check.v`, plus cleanup of non-`.v` Coq intermediates.
- Trigger condition: after successful compilation, `coq/generated/` contained `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files.
- Fix action: confirmed `proof_manual.v` contains no `Admitted.` and no top-level `Axiom`, compiled the full sequence from `QualifiedCProgramming/SeparationLogic`, then deleted all non-`.v` files under `output/verify_20260422_174132_insertion_sort/coq/`. Checked that top-level `input/` had no non-`.c`/`.v` files to remove.
- Result: final `coq/` contains only the four generated `.v` sources, `goal_check.v` compiles, and the workspace satisfies the verify success criteria.
