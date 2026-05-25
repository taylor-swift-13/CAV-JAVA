# Verify Issues

## Workspace fingerprint initially empty

- Phenomenon: `logs/workspace_fingerprint.json` started with an empty `semantic_description` and `{}` keywords.
- Trigger: this workspace was freshly initialized before verification.
- Localization: `output/verify_20260422_050657_array_init/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a nonempty semantic description and only controlled-vocabulary keyword keys and values. After successful `goal_check`, added `verification_status: ["goal_check_passed", "proof_check_passed"]`.
- Result: the fingerprint now describes the in-place array initialization loop and uses only the controlled vocabulary.

## Missing loop invariant for in-place array initialization

- Phenomenon: the active annotated C initially had no invariant on the `for (i = 0; i < n; ++i)` loop, so symbolic execution had no stable summary of which array prefix had already been written to zero.
- Trigger: `array_init` mutates the caller-provided `IntArray::full(a, n, l)` one cell at a time, but the postcondition requires an existential final list `lr` where every valid index is zero.
- Localization: `annotated/verify_20260422_050657_array_init.c`, immediately before and inside the only loop.
- Fix action: appended detailed reasoning to `logs/annotation_reasoning.md`, then inserted this invariant:

```c
/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lr) == n@pre &&
      (forall (k: Z), (0 <= k && k < i) => lr[k] == 0) &&
      (forall (k: Z), (i <= k && k < n@pre) => lr[k] == l[k]) &&
      IntArray::full(a, n@pre, lr)
*/
```

- The invariant treats `i` as the next cell to update: `[0, i)` is already zero, and `[i, n)` still equals the original `l`.
- Result: after adding the invariant and bridge assertions, `symexec` completed successfully and generated fresh `array_init_goal.v`, `array_init_proof_auto.v`, `array_init_proof_manual.v`, and `array_init_goal_check.v`.

## Focus-cell bridge needed `missing_i` and `replace_Znth`

- Phenomenon: the generated manual proof file contained one admitted theorem:

```coq
Lemma proof_of_array_init_which_implies_wit_2 : array_init_which_implies_wit_2.
Proof. Admitted.
```

- Trigger: the post-write bridge needed to merge `IntArray.missing_i a_pre i 0 n_pre lr` and the focused cell `((a_pre + i * sizeof(INT)) # Int |-> 0)` back into `IntArray.full` with an updated logical list.
- Localization: `output/verify_20260422_050657_array_init/coq/generated/array_init_proof_manual.v`.
- Fix action: appended detailed proof reasoning to `logs/proof_reasoning.md`; added local helper lemmas for `Zlength (replace_Znth ...)`, same-index `Znth`, and different-index `Znth`; then proved the theorem by choosing `lr' = replace_Znth i 0 lr`, applying `IntArray.missing_i_merge_to_full`, and splitting the prefix proof on `k = i`.
- Key proof shape:

```coq
Proof.
  pre_process.
  Exists (replace_Znth i 0 lr).
  entailer!.
  - sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
    entailer!.
  - intros k Hk.
    rewrite Znth_replace_Znth_diff by lia.
    ...
  - intros k Hk.
    destruct (Z.eq_dec k i) as [Heq | Hneq].
    ...
  - rewrite Zlength_replace_Znth.
    lia.
Qed.
```

- Result: `array_init_proof_manual.v` compiles and `rg -n "Admitted\\.|^Axiom\\b" array_init_proof_manual.v` returns no matches.

## Final compile and cleanup

- Phenomenon: successful Coq compilation produced non-source artifacts (`.vo`, `.vos`, `.vok`, `.glob`, `.aux`) under `coq/generated/`.
- Trigger: the verify workflow requires compiling the current generated files and then removing non-`.v` Coq artifacts before declaring success.
- Localization: `output/verify_20260422_050657_array_init/coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` paths and workspace-specific `-Q "$ORIG" ""` plus `-R "$GEN" SimpleC.EE.CAV.verify_20260422_050657_array_init`; then deleted all files under `coq/` whose names do not end in `.v`.
- Result: `array_init_goal.v`, `array_init_proof_auto.v`, `array_init_proof_manual.v`, and `array_init_goal_check.v` all compiled successfully, and `find coq -type f ! -name '*.v'` prints no files.
