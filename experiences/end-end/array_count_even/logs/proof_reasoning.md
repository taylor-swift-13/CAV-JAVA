## 2026-04-22 03:15:14 +0800 - Manual witnesses after successful symexec

Fresh `symexec` succeeded on the active annotated file and generated:

- `coq/generated/array_count_even_goal.v`
- `coq/generated/array_count_even_proof_auto.v`
- `coq/generated/array_count_even_proof_manual.v`
- `coq/generated/array_count_even_goal_check.v`

The generated manual proof file contains five admitted obligations:

```coq
Lemma proof_of_array_count_even_safety_wit_6 : array_count_even_safety_wit_6.
Proof. Admitted.

Lemma proof_of_array_count_even_entail_wit_1 : array_count_even_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_count_even_entail_wit_2_1 : array_count_even_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_count_even_entail_wit_2_2 : array_count_even_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_count_even_entail_wit_3 : array_count_even_entail_wit_3.
Proof. Admitted.
```

The relevant goal shapes in `array_count_even_goal.v` are:

```coq
Definition array_count_even_safety_wit_6 :=
forall ... cnt i,
  [| Znth i l 0 % 2 = 0 |] && [| i < n_pre |] && ...
  [| cnt = array_count_even_spec (sublist 0 i l) |] &&
  [| Zlength l = n_pre |] && IntArray.full a_pre n_pre l ** ...
|-- [| cnt + 1 <= INT_MAX |] && [| INT_MIN <= cnt + 1 |].

Definition array_count_even_entail_wit_2_1 :=
forall ... cnt i,
  [| Znth i l 0 % 2 = 0 |] && ...
|-- [| cnt + 1 = array_count_even_spec (sublist 0 (i + 1) l) |] && ...

Definition array_count_even_entail_wit_2_2 :=
forall ... cnt i,
  [| Znth i l 0 % 2 <> 0 |] && ...
|-- [| cnt = array_count_even_spec (sublist 0 (i + 1) l) |] && ...

Definition array_count_even_entail_wit_3 :=
forall ... cnt i,
  [| i >= n_pre |] && [| 0 <= i |] && [| i <= n_pre |] &&
  [| cnt = array_count_even_spec (sublist 0 i l) |] &&
  [| Zlength l = n_pre |] && IntArray.full a_pre n_pre l
|-- [| i = n_pre |] && [| cnt = array_count_even_spec l |] && ...
```

The minimal `pre_process; entailer!` skeleton is enough for the initialization witness, but not enough for the prefix-extension and overflow-safety witnesses.  The reusable proof pattern from the earlier same-function workspace `archieve/output_backup_20260422_011624/verify_20260422_012900_10_array_count_even/coq/generated/array_count_even_proof_manual.v` matches the current generated goals exactly except for the workspace import path.  I will copy the proof structure into this workspace:

- Add `array_count_even_spec_app_single` to rewrite `array_count_even_spec (sublist 0 i l ++ [Znth i l 0])`.
- Add `array_count_even_spec_bounds` to prove `0 <= cnt <= i` for the overflow safety witness after substituting the prefix-count invariant.
- For `entail_wit_2_1` and `entail_wit_2_2`, rewrite `sublist 0 (i + 1) l` with `sublist_split`, normalize the singleton with `sublist_single`, then use the current branch fact about `Z.rem`.
- For `entail_wit_3`, derive `i = n_pre` by `lia`, rewrite the prefix length with `Zlength l = n_pre`, and use `sublist_self`.

This is a proof-only change in `coq/generated/array_count_even_proof_manual.v`; no annotation change is needed because the witnesses already contain the required prefix-count invariant, array ownership, and exit facts.
