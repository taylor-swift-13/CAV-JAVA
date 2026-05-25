## 2026-04-22 21:23 CST - Manual proof plan after successful symexec

Fresh `symexec` succeeded on the active annotated C and generated five manual obligations in `coq/generated/remove_duplicates_sorted_proof_manual.v`:

```coq
Lemma proof_of_remove_duplicates_sorted_entail_wit_1 : remove_duplicates_sorted_entail_wit_1.
Lemma proof_of_remove_duplicates_sorted_entail_wit_2_1 : remove_duplicates_sorted_entail_wit_2_1.
Lemma proof_of_remove_duplicates_sorted_entail_wit_2_2 : remove_duplicates_sorted_entail_wit_2_2.
Lemma proof_of_remove_duplicates_sorted_return_wit_1 : remove_duplicates_sorted_return_wit_1.
Lemma proof_of_remove_duplicates_sorted_return_wit_2 : remove_duplicates_sorted_return_wit_2.
```

The current `goal.v` shows these are pure list/array-summary obligations rather than missing heap shape: the invariant has preserved `IntArray.full`, `Zlength(lc) == n_pre`, `j == Zlength(remove_duplicates_sorted_spec(sublist 0 i l))`, prefix pointwise equality, and unread suffix equality. Therefore this is proof-stage work, not an annotation fix.

The proof needs local helper lemmas for four recurring facts: equality of lists by `Znth`, `replace_Znth` length/index behavior after the write `a[j] = a[i]`, the snoc recurrence for `remove_duplicates_sorted_spec`, and normalization of `sublist 0 (Zlength l) l`. The previous exact verification used the same invariant; I will reuse that proof pattern but adapt it to this input file's helper name `remove_duplicates_sorted_cons` and this workspace's final contract, which asks for `sublist(0, j, lr) = remove_duplicates_sorted_spec(l)` rather than an explicit `lr = app(spec, t)`.

Expected witness handling:

- `entail_wit_1`: choose `lc = l`; prove the singleton prefix equals `[Znth 0 l 0]` and the prefix pointwise property.
- `entail_wit_2_1`: in the branch where `a[i] != a[j - 1]`, choose `replace_Znth j (Znth i lc 0) lc`; prove the next spec is the old spec appended with `Znth i l 0`.
- `entail_wit_2_2`: in the equal branch, choose the unchanged `lc`; prove the next spec equals the old spec.
- `return_wit_1`: with `n_pre = 0`, prove `l = nil` and choose `lr = l`.
- `return_wit_2`: exit gives `i_2 = n_pre`; rewrite `sublist 0 n_pre l` to `l`, choose `lr = lc`, and prove `sublist 0 j lc` equals the spec by list equality from the invariant's pointwise prefix fact.

## 2026-04-22 21:25 CST - Return witness length-side-condition fix

First compile after adapting the reused proof failed in `proof_of_remove_duplicates_sorted_entail_wit_2_1` because the generated VC names the write index `j_2`, while the reused proof still referred to `j` in the unequal branch. I changed the branch-local references in the proof to `j_2`; this is a proof-script naming alignment only and does not change any VC.

The next compile reached `proof_of_remove_duplicates_sorted_return_wit_2` and failed at:

```coq
rewrite Znth_sublist by lia.
```

with `Cannot find witness`. The target at that point is the prefix equality `sublist 0 j lc = remove_duplicates_sorted_spec l`. The side condition for `Znth_sublist` needs the length of `sublist 0 j lc` to be explicitly reduced before `lia` can use the introduced index bound `0 <= k < Zlength (sublist 0 j lc)`. I added a local fact `Hsub_len : Zlength (sublist 0 j lc) = j` in both the length and pointwise branches, rewrote `Hk` with it, and then applied the invariant prefix fact `H6`.
