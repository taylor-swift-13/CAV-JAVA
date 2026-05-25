## 2026-04-22 03:26:00 +0800 - Manual witnesses after successful symexec

Fresh `symexec` succeeded on the active annotated file and generated:

- `coq/generated/array_count_greater_than_k_goal.v`
- `coq/generated/array_count_greater_than_k_proof_auto.v`
- `coq/generated/array_count_greater_than_k_proof_manual.v`
- `coq/generated/array_count_greater_than_k_goal_check.v`

The manual proof file contains five admitted obligations:

```coq
Lemma proof_of_array_count_greater_than_k_safety_wit_3 : array_count_greater_than_k_safety_wit_3.
Proof. Admitted.

Lemma proof_of_array_count_greater_than_k_entail_wit_1 : array_count_greater_than_k_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_count_greater_than_k_entail_wit_2_1 : array_count_greater_than_k_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_count_greater_than_k_entail_wit_2_2 : array_count_greater_than_k_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_count_greater_than_k_entail_wit_3 : array_count_greater_than_k_entail_wit_3.
Proof. Admitted.
```

The corresponding goal shapes in `array_count_greater_than_k_goal.v` are pure list/arithmetic obligations after the separation logic framing is discharged:

```coq
Definition array_count_greater_than_k_safety_wit_3 := ... 
  [| Znth i l 0 > k_pre |] && [| i < n_pre |] &&
  [| cnt = array_count_greater_than_k_spec (sublist 0 i l) k_pre |] ...
|-- [| cnt + 1 <= INT_MAX |] && [| INT_MIN <= cnt + 1 |].

Definition array_count_greater_than_k_entail_wit_2_1 := ...
|-- [| cnt + 1 =
        array_count_greater_than_k_spec (sublist 0 (i + 1) l) k_pre |] && ...

Definition array_count_greater_than_k_entail_wit_2_2 := ...
|-- [| cnt =
        array_count_greater_than_k_spec (sublist 0 (i + 1) l) k_pre |] && ...

Definition array_count_greater_than_k_entail_wit_3 := ...
|-- [| i = n_pre |] &&
    [| cnt = array_count_greater_than_k_spec l k_pre |] && ...
```

This is not an annotation problem: the invariant already provides the prefix-count equality, the array ownership, the range facts, and the loop-exit facts. The remaining work is the same proof pattern as the completed `array_count_even` workspace, with the element contribution controlled by `Z_gt_dec (Znth i l 0) k_pre` rather than `Z.eq_dec (Z.rem ...) 0`.

I will add two local helper lemmas:

```coq
Lemma array_count_greater_than_k_spec_app_single :
  forall (l : list Z) (x k : Z),
    array_count_greater_than_k_spec (l ++ x :: nil) k =
    array_count_greater_than_k_spec l k + (if Z_gt_dec x k then 1 else 0).

Lemma array_count_greater_than_k_spec_bounds :
  forall (l : list Z) (k : Z),
    0 <= array_count_greater_than_k_spec l k <= Zlength l.
```

The main witness scripts should then remain short: use `entailer!` for framing, rewrite `sublist 0 (i + 1) l` as `sublist 0 i l ++ [Znth i l 0]` for the branch-preservation cases, destruct `Z_gt_dec` using the branch hypothesis, and rewrite `sublist 0 n_pre l` to `l` for loop exit.
