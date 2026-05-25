# Issues

## Empty workspace fingerprint placeholder

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: this workspace had only the initialized prompt/stdout/stderr logs, `original/array_min.c`, and the placeholder fingerprint when verification began.
- Localization: `output/verify_20260422_060249_array_min/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a nonempty semantic description and only controlled-vocabulary keyword keys and values. Because the vocabulary does not include `return_min`, I omitted `semantic_intent` instead of inventing a new value. After verification succeeded, I added `verification_status: ["goal_check_passed", "proof_check_passed"]`.
- Result: the fingerprint is useful for retrieval and conforms to the controlled vocabulary.

Relevant final keyword fragment:

```json
"keywords": {
  "algorithm_family": "selection",
  "control_flow": "for_loop",
  "data_shape": "array",
  "proof_pattern": ["loop_invariant", "range_bound", "heap_reasoning"],
  "numeric_properties": "int_range",
  "edge_case_behavior": "empty_loop_possible",
  "verification_status": ["goal_check_passed", "proof_check_passed"]
}
```

## Missing loop invariant for prefix-min scan

- Phenomenon: the active annotated file initially matched `input/array_min.c` and had no `Inv` before the only `for` loop.
- Trigger: `array_min` returns a value that must both occur in the array and be less than or equal to every array element. Without a loop invariant, the verifier has no way to carry the occurrence witness and prefix lower-bound fact across iterations.
- Localization: `annotated/verify_20260422_060249_array_min.c`, immediately before `for (i = 1; i < n; ++i)`.
- Fix action: added an invariant describing the already-scanned prefix `[0, i)`: bounds `1 <= i <= n`, unchanged `a` and `n`, preserved `IntArray::full(a, n, l)`, an existential index `idx` in the prefix with `l[idx] == ret`, and a universal fact that `ret <= l[j]` for every processed `j`.
- Result: rerunning `symexec` on the updated annotated file succeeded and generated fresh `array_min_goal.v`, `array_min_proof_auto.v`, `array_min_proof_manual.v`, and `array_min_goal_check.v`.

Relevant annotation:

```c
/*@ Inv
      1 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      Zlength(l) == n &&
      (exists idx, 0 <= idx && idx < i && l[idx] == ret) &&
      (forall (j: Z), (0 <= j && j < i) => ret <= l[j]) &&
      IntArray::full(a, n, l)
*/
for (i = 1; i < n; ++i) {
```

Relevant `symexec` log ending:

```text
End of symbolic execution of function array_min
Successfully finished symbolic execution
symexec_elapsed=1
symexec_status=0
```

## Manual proof obligations for existential prefix witnesses

- Phenomenon: after successful `symexec`, `coq/generated/array_min_proof_manual.v` contained two admitted lemmas, `proof_of_array_min_entail_wit_1` and `proof_of_array_min_entail_wit_2_1`.
- Trigger: these obligations choose the existential witness index for invariant initialization and for the branch where the current element becomes the new minimum.
- Localization: `output/verify_20260422_060249_array_min/coq/generated/array_min_proof_manual.v`.
- Fix action: replaced both `Admitted.` bodies with proofs. Initialization chooses `Exists 0`. The branch proof chooses `Exists i` and splits any `j < i + 1` into `j = i` or `j < i`; the old universal invariant and the branch inequality `Znth i l 0 < ret` prove the old-prefix case by `lia`.
- Result: `array_min_proof_manual.v` now contains no `Admitted.` and no `Axiom`.

Relevant proof shape:

```coq
Lemma proof_of_array_min_entail_wit_2_1 : array_min_entail_wit_2_1.
Proof.
  unfold array_min_entail_wit_2_1.
  intros.
  Exists i.
  entailer!.
  intros j Hj.
  destruct (Z.eq_dec j i) as [Heq | Hneq].
  - subst j. lia.
  - assert (Hj_old : 0 <= j /\ j < i) by lia.
    specialize (H8 j Hj_old).
    lia.
Qed.
```

## Brittle proof-state matching and generated hypothesis numbering

- Phenomenon: the first manual compile failed with `Error: No matching clauses for match.` at a `match goal with` tactic intended to find the old universal prefix-min hypothesis.
- Trigger: after `entailer!`, the parsed shape of the hypothesis did not match the overly specific tactic pattern.
- Localization: `array_min_proof_manual.v`, line 43 in the first failed compile.
- Fix action: replaced the brittle `match goal` with an explicit named range fact and a direct specialization of the generated hypothesis.
- Result: the next compile exposed that the first direct guess, `H7`, was the occurrence equality rather than the universal fact:

```text
The expression "H7" of type "Znth idx_2 l 0 = ret"
cannot be applied to the term "j" : "Z"
```

I corrected the specialization to `H8 j Hj_old`, matching the actual generated hypothesis order. The following full compile succeeded through `array_min_goal_check.v`.

## Full compile replay and cleanup

- Phenomenon: successful `symexec` and a locally completed manual proof are not enough; the workflow requires compiling `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, then removing Coq intermediate files.
- Trigger: Coq compilation creates `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under the workspace `coq/` tree.
- Localization: `output/verify_20260422_060249_array_min/coq/generated/` and `logs/compile.log`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` load paths plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_060249_array_min`. No `original/array_min.v` existed, so that optional step was skipped. After successful `goal_check`, deleted every non-`.v` file under `coq/`.
- Result: all required Coq files compiled, and `find output/verify_20260422_060249_array_min/coq -type f ! -name '*.v' -print` produced no output.

Relevant compile log:

```text
compile_start: 2026-04-22T06:06:33+08:00
skip original/array_min.v: not present
compile array_min_goal.v
compile array_min_proof_auto.v
compile array_min_proof_manual.v
compile array_min_goal_check.v
compile_end: 2026-04-22T06:06:37+08:00
```
