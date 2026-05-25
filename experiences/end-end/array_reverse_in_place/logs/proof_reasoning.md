## 2026-04-22 07:46:30 +0800 - Manual proof round 1

Fresh `symexec` succeeded for the current annotated file and generated `coq/generated/array_reverse_in_place_goal.v`, `array_reverse_in_place_proof_auto.v`, `array_reverse_in_place_proof_manual.v`, and `array_reverse_in_place_goal_check.v`. The manual file contains three admitted lemmas:

```coq
Lemma proof_of_array_reverse_in_place_entail_wit_1 : array_reverse_in_place_entail_wit_1.
Lemma proof_of_array_reverse_in_place_entail_wit_2 : array_reverse_in_place_entail_wit_2.
Lemma proof_of_array_reverse_in_place_return_wit_1 : array_reverse_in_place_return_wit_1.
```

`array_reverse_in_place_entail_wit_1` initializes the invariant from `IntArray.full a_pre n_pre l`; after `pre_process`, the key pure/list obligation is that `app (rev (sublist (n_pre - 0) n_pre l)) (app (sublist 0 ((n_pre - 1) + 1) l) (rev (sublist 0 0 l))) = l`. This should follow from `sublist_self`, empty sublists, and `app_nil_l/r`.

`array_reverse_in_place_entail_wit_2` preserves the invariant after the two writes. The key generated heap list is:

```coq
replace_Znth right (Znth left cur 0)
  (replace_Znth left (Znth right cur 0) cur)
```

where `cur = rev(sublist (n_pre - left) n_pre l) ++ sublist left (right + 1) l ++ rev(sublist 0 left l)`. Under `left < right`, `right = n_pre - 1 - left`, and `Zlength l = n_pre`, this must equal the next invariant list with `left + 1` and `right - 1`. This is a pure list/`replace_Znth` normalization problem, so I will add helper lemmas rather than change the annotation.

`array_reverse_in_place_return_wit_1` exits with `left >= right` and `right = n_pre - 1 - left`. The remaining middle segment has length zero or one; the current list expression should equal `rev l`. This is also pure list arithmetic and should be handled by a helper lemma.

First tactic plan: add local helper lemmas for the initial, step, and exit list equalities, using existing list lemmas such as `sublist_split`, `sublist_single`, `replace_Znth_app_r`, `replace_Znth_nothing`, `replace_Znth_Znth`, `sublist_nil`, and `sublist_self`; then each witness should be `pre_process`, rewrite with the helper, and `entailer!`.

## 2026-04-22 07:47:40 +0800 - Manual proof round 2

The first compile replay did not actually prove `proof_manual.v`. `logs/compile.log` showed:

```text
File ".../array_reverse_in_place_proof_manual.v", line 27, characters 32-34:
Error:
The term "H0" has type "Zlength l = n_pre" while it is expected to have type "n_pre = Zlength l".
```

Diagnosis: in `proof_of_array_reverse_in_place_entail_wit_1`, the rewrite `sublist_self` needs the length equation in the opposite orientation. This is a proof-script issue, not an annotation issue: the generated goal already contains `H0 : Zlength l = n_pre` from the precondition. The repair is to call `rewrite sublist_self by (symmetry; exact H0)`.

The same compile command also reached `goal_check.v` after the failed `proof_manual.v` because my shell block lacked fail-fast behavior. The next compile replay must use `set -e` inside the redirected block so any failed `coqc` stops immediately and reports a nonzero status.

## 2026-04-22 07:48:11 +0800 - Manual proof round 3

Using `coqtop` on `proof_of_array_reverse_in_place_entail_wit_1` showed that after `pre_process`, replacing the arithmetic endpoints, rewriting `sublist_nil`, and rewriting `sublist_self`, the remaining goal was exactly:

```coq
IntArray.full a_pre n_pre l |-- IntArray.full a_pre n_pre (l ++ nil)
```

So `entailer!` could not close the heap predicate because the list expression was not syntactically normalized. I added `rewrite app_nil_r` immediately before `entailer!`; this should turn the target heap predicate back into `IntArray.full a_pre n_pre l`.

## 2026-04-22 07:53:22 +0800 - Manual proof round 4

After adding step helper lemmas, the next compile failed inside the generic helper `replace_Znth_boundary_swap`:

```text
line 29: Error: Tactic failure: Cannot find witness.
```

The failing side condition came from `replace_Znth_nothing` at index `Zlength p`; `lia` did not automatically know `Zlength p >= 0` (nor the analogous mid-list nonnegativity later). I added explicit `pose proof (Zlength_nonneg p)` and `pose proof (Zlength_nonneg mid)` at the start of the helper, so these side conditions are available to `lia`.

## 2026-04-22 08:04:20 +0800 - Manual proof completed

The final manual proof uses local helper lemmas in `coq/generated/array_reverse_in_place_proof_manual.v`:

- `replace_Znth_boundary_swap` normalizes the two writes on a decomposed list `p ++ x :: mid ++ y :: s`.
- `reverse_step_current_decomp` and `reverse_step_target_decomp` relate the invariant list before and after one swap iteration.
- `reverse_exit_decomp` uses the strengthened invariant fact `left <= right + 1` to split loop exit into `left = right` and `left = right + 1`, then proves the invariant list equals `rev l`.

The final witness bodies are short: initialization normalizes empty/full sublists, preservation rewrites the generated double-`replace_Znth` heap list through the boundary-swap lemma, and return rewrites through `reverse_exit_decomp`. A fail-fast compile replay completed `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` successfully. `rg -n "Admitted\\.|^\\s*Axiom\\b" .../array_reverse_in_place_proof_manual.v` returned no matches.

