## Proof iteration 1

Current manual theorem:

```coq
Lemma proof_of_set_zero_which_implies_wit_2 : set_zero_which_implies_wit_2.
Proof. Admitted.
```

The witness comes from the bridge immediately after `a[i] = 0`. Its left side has the heap split as:

```coq
IntArray.missing_i a_pre i 0 n_pre lr **
((a_pre + (i * sizeof(INT))) # Int |-> 0)
```

and its right side asks for an existential `lr'` satisfying:

```coq
Zlength lr' = n_pre /\
(forall k, 0 <= k /\ k < i + 1 -> Znth k lr' 0 = 0) /\
(forall k, i + 1 <= k /\ k < n_pre -> Znth k lr' 0 = Znth k l 0) /\
IntArray.full a_pre n_pre lr'
```

This is semantically provable by choosing `lr' = replace_Znth i 0 lr`. The heap part follows from `IntArray.missing_i_merge_to_full`. The list part needs three stable helper facts: `Zlength (replace_Znth i 0 lr) = Zlength lr`, `Znth i (replace_Znth i 0 lr) 0 = 0` when `i` is in range, and `Znth k (replace_Znth i 0 lr) 0 = Znth k lr 0` when `k <> i`. The verified `examples/array_init/coq/generated/array_init_proof_manual.v` has exactly this pattern for the same post-store witness, so I will reuse that local helper structure with theorem names adjusted to `set_zero`.

Expected proof script shape:

```coq
pre_process.
Exists (replace_Znth i 0 lr).
entailer!.
- sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  entailer!.
- ...
```

The suffix branch uses the old suffix hypothesis after proving `k <> i` from `i + 1 <= k`; the prefix branch splits `k = i` and `k <> i`, using the replaced-cell lemma for the current index and the old prefix hypothesis for earlier indices.
