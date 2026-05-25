## Proof iteration 1: replace generated admitted manual witnesses

Fresh `symexec` succeeded on the latest active annotated file and generated:

- `coq/generated/array_scale_goal.v`
- `coq/generated/array_scale_proof_auto.v`
- `coq/generated/array_scale_proof_manual.v`
- `coq/generated/array_scale_goal_check.v`

The manual proof file currently contains four admitted obligations:

```coq
Lemma proof_of_array_scale_safety_wit_2 : array_scale_safety_wit_2.
Proof. Admitted.

Lemma proof_of_array_scale_entail_wit_1 : array_scale_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_scale_entail_wit_2 : array_scale_entail_wit_2.
Proof. Admitted.

Lemma proof_of_array_scale_return_wit_1 : array_scale_return_wit_1.
Proof. Admitted.
```

The generated goals have the same prefix/suffix shape as the verified `array_negate` example. The main differences are:

- the written expression is `(Znth i la 0) * k_pre` instead of `-(Znth i la 0)`;
- the overflow safety witness uses the contract hypothesis `forall i, 0 <= i < n_pre -> INT_MIN <= Znth i la 0 * k_pre <= INT_MAX`;
- loop preservation must normalize `replace_Znth i_2 (Znth i_2 la 0 * k_pre) (l1_2 ++ l2_2)` into `(l1_2 ++ [Znth i_2 la 0 * k_pre]) ++ sublist (i_2 + 1) n_pre lo`.

Planned proof shape:

- `safety_wit_2`: `pre_process; entailer!; pose proof` the overflow hypothesis at the current `i`; solve both range goals with `lia`.
- `entail_wit_1`: instantiate `l2 := lo` and `l1 := nil`; `entailer!` discharges the empty-prefix and full-output facts.
- `entail_wit_2`: first prove `l2_2 = sublist i_2 n_pre lo` by extensionality using the suffix invariant. Then choose `sublist (i_2 + 1) n_pre lo` as the new suffix and `l1_2 ++ [Znth i_2 la 0 * k_pre]` as the new prefix. Normalize `replace_Znth` across the app boundary and prove the new prefix relation by splitting `t < i_2` versus `t = i_2`.
- `return_wit_1`: use the exit facts to get `i_3 = n_pre`, choose `app l1 l2` as the result list, and prove the element relation from the completed-prefix invariant.

This should not require changing annotations again because the generated goals already include input heap preservation, output heap shape, scalar `k_pre`, and the full pointwise semantic relation needed by the postcondition.

## Proof iteration 1 result: full replay passed

After replacing the four generated `Admitted.` placeholders with concrete proofs, the fail-fast compile template was run from `QualifiedCProgramming/SeparationLogic`:

```text
compiled array_scale_goal.v
compiled array_scale_proof_auto.v
compiled array_scale_proof_manual.v
compiled array_scale_goal_check.v
```

The final `proof_manual.v` check for `Admitted.` and top-level `Axiom` declarations returned no matches:

```bash
rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/array_scale_proof_manual.v
```

The proof therefore closes all manual witnesses required by `array_scale_goal_check.v`. The automatically generated `array_scale_proof_auto.v` still contains generated `Admitted.` bodies, as is normal for this workflow's auto module; the completion criterion here is that `goal_check.v` includes both auto and manual modules and compiles successfully, and that `proof_manual.v` itself has no remaining admissions or new axioms.
