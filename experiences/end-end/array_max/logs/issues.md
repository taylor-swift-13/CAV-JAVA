# Issues

## Fingerprint initialization

- Phenomenon: the initialized `logs/workspace_fingerprint.json` had an empty `semantic_description` and `{}` keywords.
- Trigger: the workspace bootstrap left task-specific semantic classification blank.
- Localization: `output/verify_20260422_055419_array_max/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md`, then filled a non-empty semantic description and controlled-vocabulary keywords. The classification describes `array_max` as a read-only array/pointer selection scan with `for_loop`, `if`, `return_max`, `preserve_input`, `loop_invariant`, `case_split`, `range_bound`, and `heap_reasoning`.
- Result: the fingerprint now has non-empty semantic fields using only controlled key/value names. After final compilation, `verification_status` was updated with `goal_check_passed`, `manual_witness_needed`, `auto_proof_contains_admitted`, and `generated_goal_contains_axioms`.

## Missing loop invariant and loop-exit assertion

- Phenomenon: the active annotated C initially had no `Inv` before `for (i = 1; i < n; ++i)` and no assertion after loop exit:

```c
int i;
int ret = a[0];

for (i = 1; i < n; ++i) {
    if (a[i] > ret) {
        ret = a[i];
    }
}

return ret;
```

- Trigger: the postcondition requires both an existential witness showing the return value is some `l[i]` and a universal bound showing every `l[i] <= __return`. Without an invariant, symbolic execution has no prefix maximum facts to preserve across the scan.
- Localization: `annotated/verify_20260422_055419_array_max.c`, immediately before and after the `for` loop.
- Fix: added a prefix maximum invariant at the loop control point and a minimal loop-exit assertion:

```c
/*@ Inv
      1 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      (exists j, 0 <= j && j < i && l[j] == ret) &&
      (forall (j: Z), (0 <= j && j < i) => l[j] <= ret) &&
      IntArray::full(a, n, l)
*/
for (i = 1; i < n; ++i) {
```

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      (exists j, 0 <= j && j < n && l[j] == ret) &&
      (forall (j: Z), (0 <= j && j < n) => l[j] <= ret) &&
      IntArray::full(a, n, l)
*/
return ret;
```

- Result: rerunning `symexec` with the current annotated file succeeded and generated fresh `array_max_goal.v`, `array_max_proof_auto.v`, `array_max_proof_manual.v`, and `array_max_goal_check.v`.

## Symexec command and generated files

- Phenomenon: this workspace initially contained only `original/array_max.c` and logs; there were no generated Coq files.
- Trigger: verification had to be resumed manually inside the existing workspace.
- Localization: `output/verify_20260422_055419_array_max/coq/generated/`.
- Fix: created `coq/generated/`, cleared stale generated targets if present, and ran:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --goal-file=output/verify_20260422_055419_array_max/coq/generated/array_max_goal.v \
  --proof-auto-file=output/verify_20260422_055419_array_max/coq/generated/array_max_proof_auto.v \
  --proof-manual-file=output/verify_20260422_055419_array_max/coq/generated/array_max_proof_manual.v \
  --goal-check-file=output/verify_20260422_055419_array_max/coq/generated/array_max_goal_check.v \
  --input-file=annotated/verify_20260422_055419_array_max.c \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_055419_array_max \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ended with:

```text
Symbolic Execution into function array_max
End of symbolic execution of function array_max
Successfully finished symbolic execution
```

## Manual witness proof placeholders

- Phenomenon: fresh `coq/generated/array_max_proof_manual.v` contained two forbidden placeholders:

```coq
Lemma proof_of_array_max_entail_wit_1 : array_max_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_max_entail_wit_2_1 : array_max_entail_wit_2_1.
Proof. Admitted.
```

- Trigger: `symexec` left two pure entailments to manual proof. `array_max_entail_wit_1` initializes the prefix maximum invariant after `ret = a[0]` and `i = 1`; `array_max_entail_wit_2_1` preserves it in the branch where `a[i] > ret`.
- Localization: `output/verify_20260422_055419_array_max/coq/generated/array_max_proof_manual.v`.
- Fix: replaced the placeholders with direct proofs. The initialization proof uses witness `0`; the branch-preservation proof uses witness `i` and proves the new universal bound by splitting whether the arbitrary prefix index equals `i`:

```coq
Lemma proof_of_array_max_entail_wit_1 : array_max_entail_wit_1.
Proof.
  unfold array_max_entail_wit_1.
  intros.
  Exists 0.
  entailer!.
  intros j Hj.
  assert (j = 0) by lia.
  subst j.
  lia.
Qed.

Lemma proof_of_array_max_entail_wit_2_1 : array_max_entail_wit_2_1.
Proof.
  unfold array_max_entail_wit_2_1.
  intros.
  Exists i.
  entailer!.
  intros j Hj.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j. lia.
  - assert (0 <= j /\ j < i) by lia.
    specialize (H6 j H9).
    lia.
Qed.
```

- Result: `array_max_proof_manual.v` contains no `Admitted.` and no newly added `Axiom`.

## Manual proof hypothesis numbering corrections

- Phenomenon: the first compile of the edited manual proof failed at line 43:

```text
Error: Illegal application (Non-functional construction):
The expression "H5" of type "Znth j_3 l 0 = ret"
cannot be applied to the term "j" : "Z"
```

- Trigger: the script initially called `specialize (H5 j H0)`, but `H5` was the witness equality, not the old quantified prefix-bound invariant.
- Localization: `coq/generated/array_max_proof_manual.v`, theorem `proof_of_array_max_entail_wit_2_1`.
- Fix: changed the quantified invariant reference from `H5` to `H6`.
- Result: the proof advanced to the next naming issue.

- Phenomenon: the second compile failed at the same theorem:

```text
H0 : i < n_pre
H9 : 0 <= j < i
The term "H0" has type "i < n_pre" while it is expected to have type "0 <= j < i".
```

- Trigger: after `assert (0 <= j /\ j < i) by lia`, Coq named the asserted range `H9`, while the script still passed unrelated loop-bound hypothesis `H0`.
- Localization: `coq/generated/array_max_proof_manual.v`, theorem `proof_of_array_max_entail_wit_2_1`.
- Fix: changed `specialize (H6 j H0)` to `specialize (H6 j H9)`.
- Result: recompiling `array_max_goal.v`, `array_max_proof_auto.v`, `array_max_proof_manual.v`, and `array_max_goal_check.v` succeeded.

## Final compile and cleanup

- Phenomenon: standard Coq compilation produced `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` byproducts under `coq/generated/`.
- Trigger: running the full compile template for generated files.
- Localization: `output/verify_20260422_055419_array_max/coq/generated/`.
- Fix: after successful compilation, remove all non-`.v` files under the workspace `coq/` tree.
- Result: cleanup was performed after the successful compile check; no non-`.v` files remain under this workspace `coq/` tree.
