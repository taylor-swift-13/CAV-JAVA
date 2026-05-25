## Proof iteration 1: replace_Znth list-update witnesses

Current generated manual file:

```coq
Lemma proof_of_string_set_a_entail_wit_2 : string_set_a_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_set_a_return_wit_1 : string_set_a_return_wit_1.
Proof. Admitted.
```

The relevant generated goals are pure/list update obligations over a `CharArray.full` resource that has already been updated by symbolic execution:

```coq
Definition string_set_a_entail_wit_2 :=
forall (s_pre n_pre : Z) (l lr_2 : list Z) (i : Z),
  ... CharArray.full s_pre (n_pre + 1) (replace_Znth i 97 lr_2)
|--
  EX lr,
    [| 0 <= i + 1 |] &&
    [| i + 1 <= n_pre |] &&
    [| Zlength lr = n_pre + 1 |] &&
    [| forall k, 0 <= k /\ k < i + 1 -> Znth k lr 0 = 97 |] &&
    [| forall k, i + 1 <= k /\ k < n_pre + 1 -> Znth k lr 0 = Znth k l 0 |] &&
    ... CharArray.full s_pre (n_pre + 1) lr.
```

This is semantically provable with witness `replace_Znth i 97 lr_2`. The old invariant gives the prefix property for `k < i` and suffix property for `i <= k`; the write at `i` supplies the new same-index case. The first quantified subgoal after `entailer!` is expected to be the suffix property, so it must use `Znth_replace_Znth_diff` with `k <> i`; the second quantified subgoal is the prefix property and splits on `k = i`.

The return witness has shape:

```coq
Definition string_set_a_return_wit_1 :=
forall (s_pre n_pre : Z) (l lr_2 : list Z) (i_2 : Z),
  ... i_2 >= n_pre ... i_2 <= n_pre ...
  CharArray.full s_pre (n_pre + 1) (replace_Znth n_pre 0 lr_2)
|--
  EX lr,
    [| Zlength lr = n_pre + 1 |] &&
    [| forall i, 0 <= i /\ i < n_pre -> Znth i lr 0 = 97 |] &&
    [| Znth n_pre lr 0 = 0 |] &&
    CharArray.full s_pre (n_pre + 1) lr.
```

This is semantically provable after deriving `i_2 = n_pre` by arithmetic and choosing witness `replace_Znth n_pre 0 lr_2`. The terminator equality uses the same-index replacement lemma; the prefix property uses the different-index lemma because `k < n_pre`; the length property uses `Zlength_replace_Znth`.

The proof needs local helper lemmas for `replace_nth` / `replace_Znth` length, same-index lookup, and different-index lookup. These are the same reusable lemmas as the nearby verified `string_fill_char` workspace, specialized here by the generated goal to the constant value `97`; no new axioms are needed.
