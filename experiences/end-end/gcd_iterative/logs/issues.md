## Issue 1: fingerprint started with empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` had `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the verify workflow requires a useful fingerprint early in the task, and the user explicitly required reading `doc/retrieval/INDEX.md` before updating it.
- Localization: `output/verify_20260422_170350_gcd_iterative/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a non-empty semantic description for the scalar Euclidean while loop and used only controlled vocabulary keys/values: `algorithm_family`, `control_flow`, `data_shape`, `proof_pattern`, `numeric_properties`, `edge_case_behavior`, and after success `verification_status`.
- Result: the fingerprint is useful for retrieval and records `goal_check_passed`, `proof_check_passed`, and `manual_witness_needed`.

## Issue 2: loop needed a shared-gcd invariant

- Phenomenon: the active annotated copy initially matched the input C and had no invariant before:

```c
while (b != 0) {
    r = a % b;
    a = b;
    b = r;
}
```

- Trigger: both `a` and `b` are mutated, but the postcondition refers to the original pair through `gcd_iterative_spec(a@pre, b@pre, __return)`.
- Localization: `annotated/verify_20260422_170350_gcd_iterative.c`.
- Fix action: added an existential invariant that names the shared gcd value `g` and relates both the original pair and current pair to it:

```c
/*@ Inv exists g,
      0 <= a &&
      0 <= b &&
      0 < a + b &&
      gcd_iterative_spec(a@pre, b@pre, g) &&
      gcd_iterative_spec(a, b, g)
*/
```

- Result: rerunning `symexec` on the updated annotated file succeeded and generated fresh `gcd_iterative_goal.v`, `gcd_iterative_proof_auto.v`, `gcd_iterative_proof_manual.v`, and `gcd_iterative_goal_check.v`.

## Issue 3: manual proofs were required after successful symexec

- Phenomenon: `coq/generated/gcd_iterative_proof_manual.v` contained three generated placeholders:

```coq
Lemma proof_of_gcd_iterative_entail_wit_1 : gcd_iterative_entail_wit_1.
Proof. Admitted.

Lemma proof_of_gcd_iterative_entail_wit_2 : gcd_iterative_entail_wit_2.
Proof. Admitted.

Lemma proof_of_gcd_iterative_return_wit_1 : gcd_iterative_return_wit_1.
Proof. Admitted.
```

- Trigger: the invariant introduced an existential shared gcd witness, so initialization, preservation, and loop-exit return all required pure Coq reasoning.
- Localization: `coq/generated/gcd_iterative_proof_manual.v`.
- Fix action: added local helper lemmas `gcd_iterative_step` and `gcd_iterative_zero_right`, then replaced all three `Admitted.` placeholders with concrete proofs using `pre_process`, `Exists`, `entailer!`, `sep_apply store_int_undef_store_int`, `Z.gcd_rem`, `Z.rem_mod_nonneg`, `Z.mod_pos_bound`, and `Z.gcd_0_r_nonneg`.
- Result: `rg -n "Admitted\\.|^Axiom\\b" coq/generated/gcd_iterative_proof_manual.v` reports no matches.

## Issue 4: generated C `%` notation is `Z.rem`, not Coq `Z.modulo`

- Phenomenon: early proof attempts using `Z.gcd_mod` and helper conclusions written with `a mod b` failed. Representative errors included:

```text
Error: Found no subterm matching "Zgcd (?M3000 mod ?M3001) ?M3001"
in the current goal.

Unable to unify "a mod b" with "a % b".
```

- Trigger: under `Local Open Scope sac`, generated C remainder syntax `a % ( b )` prints as `%` but is `Z.rem a b`; Coq's `a mod b` keyword is `Z.modulo a b`.
- Localization: `coq/generated/gcd_iterative_proof_manual.v`, helper lemma `gcd_iterative_step`, and preservation witness `proof_of_gcd_iterative_entail_wit_2`.
- Fix action: changed the helper conclusion to:

```coq
gcd_iterative_spec b (a % ( b )) g
```

and used `Z.gcd_rem` for gcd preservation. For range goals, rewrote `Z.rem` to nonnegative modulo with:

```coq
Z.rem_mod_nonneg a b H0 Hbpos
```

then applied `Z.mod_pos_bound`.
- Result: the preservation witness compiled successfully.

## Issue 5: return witness needed explicit loop-exit substitution

- Phenomenon: the return proof initially failed with:

```text
Tactic failure: Cannot find witness.
```

at:

```coq
eapply gcd_iterative_zero_right; eauto; lia.
```

- Trigger: the context had `H : b = 0` and `H4 : gcd_iterative_spec a b g`; the helper required exactly `gcd_iterative_spec a 0 g`, and `eauto` did not perform the needed substitution.
- Localization: `proof_of_gcd_iterative_return_wit_1` in `coq/generated/gcd_iterative_proof_manual.v`.
- Fix action: substituted the exit equality before applying the helper:

```coq
subst b.
eapply gcd_iterative_zero_right; [lia | exact H4].
```

- Result: `proof_manual.v` compiled.

## Issue 6: final compile and cleanup required after proof success

- Phenomenon: successful manual proofs alone are not enough; the workflow requires compiling `original/gcd_iterative.v`, generated `goal`, `proof_auto`, `proof_manual`, and `goal_check`, then removing non-`.v` Coq intermediates.
- Trigger: verify completion criteria require `goal_check.v` to compile under the workspace load path and no non-`.v` files to remain under the workspace `coq/` tree.
- Localization: `logs/compile_replay.log` and `output/verify_20260422_170350_gcd_iterative/coq/generated/`.
- Fix action: ran the documented compile template from `QualifiedCProgramming/SeparationLogic` with `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_170350_gcd_iterative`, then deleted all non-`.v` files under the workspace `coq/` directory.
- Result: `logs/compile_replay.log` records successful compilation through `goal_check`, and `find output/verify_20260422_170350_gcd_iterative/coq -type f ! -name '*.v'` returns no files.
