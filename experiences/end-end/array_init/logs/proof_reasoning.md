## 2026-04-22 proof round 1: prove the post-write array merge witness

After a successful `symexec`, the generated manual file contains exactly one admitted theorem:

```coq
Lemma proof_of_array_init_which_implies_wit_2 : array_init_which_implies_wit_2.
Proof. Admitted.
```

The target from `array_init_goal.v` is:

```coq
Definition array_init_which_implies_wit_2 :=
forall a_pre n_pre l lr i,
  [| 0 <= i |] && [| i < n_pre |] &&
  [| n_pre = Zlength l |] &&
  [| Zlength lr = n_pre |] &&
  [| forall k, 0 <= k /\ k < i -> Znth k lr 0 = 0 |] &&
  [| forall k, i <= k /\ k < n_pre -> Znth k lr 0 = Znth k l 0 |] &&
  IntArray.missing_i a_pre i 0 n_pre lr **
  ((a_pre + i * sizeof(INT)) # Int |-> 0)
|--
  EX lr',
    [| Zlength lr' = n_pre |] &&
    [| forall k, 0 <= k /\ k < i + 1 -> Znth k lr' 0 = 0 |] &&
    [| forall k, i + 1 <= k /\ k < n_pre -> Znth k lr' 0 = Znth k l 0 |] &&
    IntArray.full a_pre n_pre lr'.
```

The separation-logic part should be solved by choosing `lr' = replace_Znth i 0 lr` and applying `IntArray.missing_i_merge_to_full`, exactly like the verified `array_increment` example. The pure part needs the standard facts:

- `Zlength (replace_Znth i 0 lr) = Zlength lr`
- at index `i`, `Znth i (replace_Znth i 0 lr) 0 = 0`
- at any index `k <> i`, `Znth k (replace_Znth i 0 lr) 0 = Znth k lr 0`

I will add local helper lemmas for `replace_Znth`, then replace the admitted body with:

```coq
pre_process.
Exists (replace_Znth i 0 lr).
entailer!.
...
```

The prefix proof splits on `k = i`: the equal case uses `Znth_replace_Znth_same`; the unequal case rewrites to the old `lr` and uses the old prefix fact. The suffix proof rewrites by `Znth_replace_Znth_diff` because `k >= i + 1` implies `k <> i`, then uses the old suffix fact.
