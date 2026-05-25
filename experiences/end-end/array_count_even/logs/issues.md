# Verify Issues

## 2026-04-22 03:16:38 +0800 - Fingerprint placeholder had to be filled before verification

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: workspace initialization creates a placeholder fingerprint before the Verify agent analyzes the program.
- Location: `output/verify_20260422_031257_array_count_even/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled the semantic description with the read-only array scan behavior and used only controlled-vocabulary keywords:

```json
"algorithm_family": "counting",
"control_flow": ["for_loop", "if"],
"data_shape": "array",
"semantic_intent": "preserve_input",
"proof_pattern": ["loop_invariant", "range_bound", "heap_reasoning"],
"numeric_properties": ["nonnegative_input", "monotone_accumulator", "int_range"],
"edge_case_behavior": "empty_loop_possible"
```

- Result: the fingerprint is independently useful for retrieval and, after final verification, also records `verification_status` values `goal_check_passed`, `proof_check_passed`, `auto_proof_contains_admitted`, and `generated_goal_contains_axioms`.

## 2026-04-22 03:16:38 +0800 - Active C copy lacked the required prefix-count loop invariant

- Phenomenon: the active annotated file initially had the raw loop with no `Inv` or loop-exit assertion:

```c
int cnt = 0;

for (i = 0; i < n; ++i) {
    if (a[i] % 2 == 0) {
        cnt++;
    }
}

return cnt;
```

- Trigger: `array_count_even` is a for-loop array scan; without an invariant, symbolic execution has no way to preserve that `cnt` equals the count of even elements in the processed prefix.
- Location: `annotated/verify_20260422_031257_array_count_even.c`.
- Fix action: appended detailed reasoning to `logs/annotation_reasoning.md`, then added an invariant at the for-loop control point and a minimal loop-exit assertion:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_even_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) { ... }

/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_even_spec(l) &&
      IntArray::full(a, n, l)
*/
return cnt;
```

- Result: rerunning `QualifiedCProgramming/linux-binary/symexec` in the same workspace succeeded. `logs/qcp_run.log` ends with `Successfully finished symbolic execution` and generated fresh `array_count_even_goal.v`, `array_count_even_proof_auto.v`, `array_count_even_proof_manual.v`, and `array_count_even_goal_check.v`.

## 2026-04-22 03:16:38 +0800 - Manual proof obligations generated after successful symexec

- Phenomenon: fresh `coq/generated/array_count_even_proof_manual.v` contained five admitted manual obligations:

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

- Trigger: the remaining VCs are pure arithmetic/list obligations around `cnt + 1` range safety, prefix extension by one array element, and rewriting the final prefix `sublist 0 n l` to `l`.
- Location: `output/verify_20260422_031257_array_count_even/coq/generated/array_count_even_proof_manual.v`.
- Fix action: appended proof reasoning to `logs/proof_reasoning.md`, reused the matching proof pattern from the earlier same-function workspace, and added two local helper lemmas plus concrete witness proofs:

```coq
Lemma array_count_even_spec_app_single :
  forall (l : list Z) (x : Z),
    array_count_even_spec (l ++ x :: nil) =
    array_count_even_spec l + (if Z.eq_dec (Z.rem x 2) 0 then 1 else 0).

Lemma array_count_even_spec_bounds :
  forall (l : list Z),
    0 <= array_count_even_spec l <= Zlength l.
```

- Result: `array_count_even_proof_manual.v` compiles successfully and `rg -n "Admitted\\.|^\\s*Axiom\\b"` finds no remaining manual admits or added top-level axioms in that file.

## 2026-04-22 03:16:38 +0800 - Full Coq replay and cleanup

- Phenomenon: verification is not complete until `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compile with the workspace load-path template, and non-`.v` Coq artifacts are removed afterward.
- Trigger: `coqc` produces `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files during replay.
- Location: `output/verify_20260422_031257_array_count_even/coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` flags, `-Q "$ORIG" ""`, and `-R "$GEN" "SimpleC.EE.CAV.verify_20260422_031257_array_count_even"`. The replay log is `logs/compile_full.log`:

```text
compiled original/array_count_even.v
compiled array_count_even_goal.v
compiled array_count_even_proof_auto.v
compiled array_count_even_proof_manual.v
compiled array_count_even_goal_check.v
compile_status: 0
```

- Result: `goal_check.v` compiled successfully. All non-`.v` files under this workspace's `coq/` directory were deleted, and a follow-up `find ... -type f ! -name '*.v'` returned no files.
