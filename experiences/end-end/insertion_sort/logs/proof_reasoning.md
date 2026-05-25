## 2026-04-22 17:46 +0800 - Manual proof plan after successful symexec

Fresh `symexec` succeeded for `annotated/verify_20260422_174132_insertion_sort.c` and generated:

```text
coq/generated/insertion_sort_goal.v
coq/generated/insertion_sort_proof_auto.v
coq/generated/insertion_sort_proof_manual.v
coq/generated/insertion_sort_goal_check.v
```

The generated manual file initially contained six admitted obligations:

```coq
Lemma proof_of_insertion_sort_entail_wit_1 : insertion_sort_entail_wit_1.
Proof. Admitted.

Lemma proof_of_insertion_sort_entail_wit_2 : insertion_sort_entail_wit_2.
Proof. Admitted.

Lemma proof_of_insertion_sort_entail_wit_3 : insertion_sort_entail_wit_3.
Proof. Admitted.

Lemma proof_of_insertion_sort_entail_wit_4_1 : insertion_sort_entail_wit_4_1.
Proof. Admitted.

Lemma proof_of_insertion_sort_entail_wit_4_2 : insertion_sort_entail_wit_4_2.
Proof. Admitted.

Lemma proof_of_insertion_sort_return_wit_1 : insertion_sort_return_wit_1.
Proof. Admitted.
```

The hard witnesses are not separation-logic ownership problems: the generated goals contain the shifted-hole state needed for insertion sort. For example, the inner-loop preservation witness has:

```coq
l_cur_2 =
  sublist 0 (j + 2) l_base_2 ++
  sublist (j + 1) i_2 l_base_2 ++
  sublist (i_2 + 1) n_pre l_base_2
```

and must prove the next state after:

```coq
replace_Znth (j + 1) (Znth j l_cur_2 0) l_cur_2
```

equals the shifted-hole representation for `j - 1`. The final insertion witnesses choose `replace_Znth (j + 1) key l_cur` as the next outer-loop ghost list and must prove four independent facts: adjacent-order preservation, permutation preservation, length preservation, and heap/local-variable cleanup. The return witness must unfold:

```coq
insertion_sort_spec l lr
```

and prove `StronglySorted Z.le lr /\ Permutation l lr`. This current contract differs from the older archived proof whose return goal was a direct `sorted_z` fact, so the return helper must derive `StronglySorted` from the adjacent-order invariant.

Planned proof edit:

- Add local `replace_Znth`, `sublist`, and shifted-hole helper lemmas.
- Prove `entail_wit_1` by choosing `l`.
- Prove `entail_wit_2` by choosing `l_outer` for both `l_cur` and `l_base` and normalizing `sublist 0 (i + 1) ++ sublist i i ++ sublist (i + 1) n`.
- Prove `entail_wit_3` with a helper showing one right-shift updates the hole representation and extends the `key < l_base[k]` range.
- Prove final insertion branches with explicit `(l_base := l_base)` and `(l_cur := l_cur)` helper instantiations to avoid Coq picking the stale outer-loop list.
- Prove `return_wit_1` by unfolding `insertion_sort_spec`, deriving `StronglySorted Z.le l_outer` from adjacent order when `n > 0`, and using the zero-length case when `n == 0`.

## 2026-04-22 17:49 +0800 - StronglySorted helper repair

First compile attempt after replacing the admissions failed in the new return helper:

```text
File ".../insertion_sort_proof_manual.v", line 480, characters 42-68:
Error: Found no subterm matching "Zlength (?M3013 :: ?M3014)" in Hk.
```

The failing helper tried to prove `StronglySorted Z.le` directly by nested induction and rewrote `Zlength_cons` inside a hypothesis `Hk` that was already about the tail list, not the cons list. After removing that rewrite, the next compile exposed the deeper issue:

```text
Unable to unify "Forall (Z.le a) l" with "Forall (Z.le a0) l".
```

The direct nested induction was using an induction hypothesis specialized to the wrong head element. I split the return proof into two helpers:

```coq
Lemma insertion_sort_adjacent_tail :
  forall h l, adjacent_order (h :: l) -> adjacent_order l.

Lemma insertion_sort_adjacent_head_forall :
  forall h l, adjacent_order (h :: l) -> Forall (Z.le h) l.
```

The actual file spells out `adjacent_order` as the generated `forall k, 0 <= k /\ k + 1 < Zlength ... -> Znth k ... <= Znth (k + 1) ...` predicate. `insertion_sort_strong_sorted_from_adjacent` now constructs `StronglySorted` by applying the tail lemma for the recursive sortedness proof and the head-forall lemma for the `Forall (Z.le h) tail` proof.

## 2026-04-22 17:51 +0800 - Regenerated hypothesis numbering repair

The next compile reached `proof_of_insertion_sort_entail_wit_3` and failed with:

```text
Error: [Focus] Wrong bullet -: Current bullet - is not finished.
```

Using `coqtop Show` after the `entailer!` state showed the current generated hypotheses:

```coq
H6  : Zlength l_base_2 = n_pre
H7  : Permutation l l_base_2
H8  : forall k_2, ...
H9  : forall k_3, j < k_3 < i_2 -> key < Znth k_3 l_base_2 0
H10 : l_cur_2 =
        sublist 0 (j + 2) l_base_2 ++
        sublist (j + 1) i_2 l_base_2 ++ sublist (i_2 + 1) n_pre l_base_2
```

The copied proof had used `H11` for the shifted-hole shape, but this current contract adds `Zlength(l) == n@pre`, so several hypothesis numbers differ from the archived proof. I changed `entail_wit_3` to use `H10` for the shape and `H9` for the shifted range fact.

The analogous final negative branch first failed with:

```text
The term "H7" has type "forall k_2 ... adjacent ..."
while it is expected to have type "Permutation l ?l'".
```

For `proof_of_insertion_sort_entail_wit_4_2`, the current numbering is:

```coq
H4 : key = Znth i l_base 0
H5 : Zlength l_base = n_pre
H6 : Permutation l l_base
H7 : adjacent order on l_base
H8 : shifted elements are greater than key
H9 : shifted-hole shape for l_cur
```

I updated the final negative-branch helper calls to pass `H9` for the shape, `H4` for the key equality, and `H6` for the permutation. After these fixes, `insertion_sort_proof_manual.v` compiled, contains no `Admitted.`, and the full sequence through `insertion_sort_goal_check.v` compiled successfully.
