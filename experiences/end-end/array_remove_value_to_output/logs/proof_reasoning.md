## 2026-04-22 07:14 proof pass 1

Fresh `symexec` succeeded on the current active annotated C and generated the four Coq files under `coq/generated/`. The generated manual file contains exactly five admitted obligations:

```coq
Lemma proof_of_array_remove_value_to_output_entail_wit_1 : array_remove_value_to_output_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_remove_value_to_output_entail_wit_2_1 : array_remove_value_to_output_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_remove_value_to_output_entail_wit_2_2 : array_remove_value_to_output_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_remove_value_to_output_entail_wit_3 : array_remove_value_to_output_entail_wit_3.
Proof. Admitted.

Lemma proof_of_array_remove_value_to_output_return_wit_1 : array_remove_value_to_output_return_wit_1.
Proof. Admitted.
```

The goal shapes are pure list/heap witnesses after framing:

```coq
array_remove_value_to_output_entail_wit_2_1:
  Znth i la 0 <> k_pre ->
  lout = replace_Znth write (Znth i la 0) lout_2
  must re-establish the invariant for sublist 0 (i + 1) la and write + 1.

array_remove_value_to_output_entail_wit_2_2:
  Znth i la 0 = k_pre ->
  lout_2 itself must re-establish the invariant for sublist 0 (i + 1) la and unchanged write.

array_remove_value_to_output_return_wit_1:
  source heap has IntArray.full out_pre n_pre lout, while the postcondition wants
  IntArray.full out_pre n_pre (app (array_remove_value_to_output_spec la k_pre) tail).
```

This is not an annotation gap: the invariant exposes the input prefix, filtered prefix length, output prefix equality, untouched suffix equality, and loop-exit equality. The remaining work is list normalization:

```coq
sublist 0 (i + 1) la = sublist 0 i la ++ [Znth i la 0]
array_remove_value_to_output_spec (xs ++ [x]) k =
  if x = k then spec xs k else spec xs k ++ [x]
Znth p (replace_Znth write x lout_2) 0
```

Planned edit to `coq/generated/array_remove_value_to_output_proof_manual.v`: add local helper lemmas for `replace_Znth` length/same/other, the filter-snoc keep/drop cases, a filter length bound, and a prefix/suffix reconstruction lemma for the return witness. Then replace the five `Admitted.` bodies with conservative scripts using `pre_process`, `Exists`, `entailer!`, explicit `sublist_split`/`sublist_single` rewrites, and `lia`.

First compile attempt after that edit failed in `proof_of_array_remove_value_to_output_entail_wit_2_1`:

```text
File ".../array_remove_value_to_output_proof_manual.v", line 187, characters 4-22:
Error: Found no subterm matching
"array_remove_value_to_output_spec (sublist 0 (i + 1) la) k_pre"
in the current goal.
```

The failing proof had just asserted:

```coq
Hspec_next :
  array_remove_value_to_output_spec (sublist 0 (i + 1) la) k_pre =
  array_remove_value_to_output_spec (sublist 0 i la) k_pre ++ [Znth i la 0]
```

After `entailer!`, the remaining prefix and length goals are normalized toward the right-hand side `old_spec ++ [Znth i la 0]`, not toward the original `sublist 0 (i + 1)` expression. The fix is to use `rewrite <- Hspec_next` in the branch goals where the current goal mentions the snoc-normalized right-hand side.

Further inspection with `coqtop` showed the more precise issue: after `entailer!` in `entail_wit_2_1`, the generated subgoals are ordered as suffix preservation, prefix preservation, filtered-length equality, and `replace_Znth` length. The prefix subgoal is:

```coq
forall p : Z,
  0 <= p < write + 1 ->
  Znth p (replace_Znth write (Znth i la 0) lout_2) 0 =
  Znth p (array_remove_value_to_output_spec (sublist 0 (i + 1) la) k_pre) 0
```

The successful proof handles the suffix goal first with `arvo_Znth_replace_Znth_other`, then rewrites the prefix goal with:

```coq
rewrite Hspec_next.
destruct (Z_lt_ge_dec p write) as [Hlt | Hge].
```

For `p < write`, `replace_Znth` is unchanged and the old prefix invariant `H9` applies. For `p = write`, `replace_Znth` gives the just-written `Znth i la 0`, and `app_Znth2`/`Znth0_cons` selects the new last element of the filtered prefix.

`entail_wit_2_2` had a different goal order: prefix preservation and then filtered-length equality. The unchanged suffix was solved by `entailer!`. The final script rewrites both remaining goals with:

```coq
Hspec_next :
  array_remove_value_to_output_spec (sublist 0 (i + 1) la) k_pre =
  array_remove_value_to_output_spec (sublist 0 i la) k_pre
```

`entail_wit_3` also had only two remaining subgoals after `entailer!`: the final prefix equality and final filtered length. Both are discharged by rewriting `sublist 0 n_pre la` to `la`.

The final `return_wit_1` uses:

```coq
Exists (sublist write n_pre lout).
```

Then `arvo_prefix_tail_rebuild` proves the heap list equality:

```coq
lout =
  array_remove_value_to_output_spec la k_pre ++ sublist write n_pre lout
```

This lets the source `IntArray.full out_pre n_pre lout` match the postcondition's `IntArray.full` shape. Full compilation completed successfully:

```text
compiled=array_remove_value_to_output.v
compiled=array_remove_value_to_output_goal.v
compiled=array_remove_value_to_output_proof_auto.v
compiled=array_remove_value_to_output_proof_manual.v
compiled=array_remove_value_to_output_goal_check.v
```

`rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/array_remove_value_to_output_proof_manual.v` produced no matches.
