# Proof Reasoning

## 2026-04-22 manual witnesses after successful `symexec`

Fresh symbolic execution succeeded for `annotated/verify_20260422_072722_array_replace_k.c` and generated:

```text
array_replace_k_goal.v
array_replace_k_proof_auto.v
array_replace_k_proof_manual.v
array_replace_k_goal_check.v
```

The generated `array_replace_k_proof_manual.v` contains four admitted obligations:

```coq
Lemma proof_of_array_replace_k_entail_wit_1 : array_replace_k_entail_wit_1.
Lemma proof_of_array_replace_k_entail_wit_2_1 : array_replace_k_entail_wit_2_1.
Lemma proof_of_array_replace_k_entail_wit_2_2 : array_replace_k_entail_wit_2_2.
Lemma proof_of_array_replace_k_return_wit_1 : array_replace_k_return_wit_1.
```

`entail_wit_1` initializes the invariant with `l1 = nil` and `l2 = l`. `entail_wit_2_1` is the branch where the current cell equals `old_k_pre`, so the heap list after assignment is `replace_Znth i new_k_pre (l1_2 ++ l2_2)` and must be rewritten to the next invariant list `l1_2 ++ [new_k_pre] ++ sublist (i + 1) n_pre l`. `entail_wit_2_2` is the non-replacement branch, so the next prefix appends the original `Znth i l 0`. `return_wit_1` uses `i_2 = n_pre`, `l2 = nil`, and the prefix relation over all indices.

The nearest successful proof pattern is archived `array_replace_negative_zero_proof_manual.v`. It has the same prefix/suffix invariant and the same four manual obligations; only the branch predicate and replacement value differ. I will adapt its local `list_eq_by_Znth` helper plus the two preservation proofs, replacing the negative/nonnegative cases with equality/inequality against `old_k_pre`.

## 2026-04-22 return witness compile mismatch

The first compile replay after inserting the adapted proof compiled `array_replace_k_goal.v` and `array_replace_k_proof_auto.v`, then failed in `array_replace_k_proof_manual.v` at the return witness with:

```text
Error: No matching clauses for match.
```

The failing proof fragment looked for the final prefix hypothesis with bound `t < n_pre`:

```coq
match goal with
| Hprefix : forall t : Z,
    0 <= t < n_pre ->
    ... |- _ => apply Hprefix; lia
end.
```

A `coqc` probe of the return witness after:

```coq
pre_process; ...; Exists l1; entailer!; intros i Hi; Show.
```

showed that `pre_process` has substituted the invariant index with `Zlength l1`; the available hypothesis is:

```coq
H5 : forall t : Z,
  0 <= t < Zlength l1 ->
  (Znth t l 0 = old_k_pre -> Znth t l1 0 = new_k_pre) /\
  (Znth t l 0 <> old_k_pre -> Znth t l1 0 = Znth t l 0)
```

The fix is to match the actual bound `Zlength l1` and let `lia` use the generated equality `Zlength l1 = n_pre`.
