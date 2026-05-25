## Workspace fingerprint initially had empty semantic metadata

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and `{}` keywords.
- Trigger: early verify workspace setup for `verify_20260423_052427_two_sum_sorted`.
- Localization: `output/verify_20260423_052427_two_sum_sorted/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a nonempty semantic description and used only controlled-vocabulary keys and values:

```json
"algorithm_family": ["search", "two_pointers"],
"control_flow": ["while_loop", "if"],
"data_shape": ["array", "pointer"],
"semantic_intent": "preserve_input",
"proof_pattern": ["loop_invariant", "case_split", "range_bound", "monotonicity", "heap_reasoning"],
"numeric_properties": ["int_range", "overflow_guard"],
"edge_case_behavior": "empty_loop_possible"
```

- Result: after final `goal_check` success, the fingerprint also records `"verification_status": ["goal_check_passed", "proof_check_passed"]`.

## Missing loop invariant for two-pointer elimination semantics

- Phenomenon: the active annotated file originally had a bare `while (left < right)` loop. Without an invariant, symbolic execution would not retain which pairs had already been ruled out, and the `return 0` postcondition requires proving every valid pair has sum different from `target`.
- Trigger: initial inspection of `annotated/verify_20260423_052427_two_sum_sorted.c`.
- Localization: immediately before the loop:

```c
while (left < right) {
    s = a[left] + a[right];
    if (s == target) {
        return 1;
    }
    if (s < target) {
        left++;
    } else {
        right--;
    }
}
```

- Fix action: added a loop invariant preserving sortedness, pair-sum range safety, pointer bounds, unchanged parameters, `IntArray::full(a, n, l)`, and two eliminated-region facts:

```c
(forall (i: Z) (j: Z),
  (0 <= i && i < left && i < j && j < n) =>
    l[i] + l[j] != target)
(forall (i: Z) (j: Z),
  (0 <= i && i < j && j < n && right < j) =>
    l[i] + l[j] != target)
```

- Result: `QualifiedCProgramming/linux-binary/symexec` completed successfully and generated fresh `two_sum_sorted_goal.v`, `two_sum_sorted_proof_auto.v`, `two_sum_sorted_proof_manual.v`, and `two_sum_sorted_goal_check.v`.

## Manual proof hypothesis names and generated conjunction shapes

- Phenomenon: the first manual proof script for `two_sum_sorted_safety_wit_4` failed:

```text
Error: Illegal application (Non-functional construction):
The expression "H2" of type "Zlength l = n_pre"
cannot be applied to the term "left" : "Z"
```

- Trigger: the script assumed a fixed hypothesis number for the pair-sum range invariant.
- Localization: `coq/generated/two_sum_sorted_proof_manual.v`, lemma `proof_of_two_sum_sorted_safety_wit_4`.
- Fix action: replaced numbered references with a `match goal` that finds the quantified range fact by shape and instantiates it with `left` and `right`:

```coq
match goal with
| Hrange: forall i j : Z, _ -> INT_MIN <= Znth i l 0 + Znth j l 0 <= INT_MAX |- _ =>
    pose proof (Hrange left right ltac:(lia)) as Hsum_range;
    lia
end.
```

- Result: `two_sum_sorted_safety_wit_4` compiled.

## Redundant tactic after `pre_process` solved invariant initialization

- Phenomenon: after fixing the safety witness, compilation failed in `proof_of_two_sum_sorted_entail_wit_1`:

```text
Error: No such goal.
```

- Trigger: `pre_process` had already solved the initialization witness; the following `entailer!` ran with no remaining goal.
- Localization: `coq/generated/two_sum_sorted_proof_manual.v`, lemma `proof_of_two_sum_sorted_entail_wit_1`.
- Fix action: removed the redundant `entailer!`, leaving:

```coq
Lemma proof_of_two_sum_sorted_entail_wit_1 : two_sum_sorted_entail_wit_1.
Proof.
  pre_process.
Qed.
```

- Result: the invariant initialization witness compiled.

## Return witness match pattern was too strict for chained inequalities

- Phenomenon: compilation then failed in `proof_of_two_sum_sorted_return_wit_2`:

```text
Error: No matching clauses for match.
```

- Trigger: the proof used a `match goal` pattern expecting flat conjunctions such as `0 <= x /\ x < left /\ x < y /\ y < n_pre`, but `coqtop` showed the generated hypotheses use chained inequality notation and grouped conjunctions:

```coq
H10 :
  forall i_7 j_7 : Z,
  (0 <= i_7 < left /\ i_7 < j_7) /\ j_7 < n_pre ->
  Znth i_7 l 0 + Znth j_7 l 0 <> target_pre
H11 :
  forall i_8 j_8 : Z,
  (0 <= i_8 < j_8 /\ j_8 < n_pre) /\ right < j_8 ->
  Znth i_8 l 0 + Znth j_8 l 0 <> target_pre
```

- Localization: `coq/generated/two_sum_sorted_proof_manual.v`, lemma `proof_of_two_sum_sorted_return_wit_2`.
- Fix action: used the concrete generated hypotheses after `pre_process; Left; entailer!`:

```coq
destruct (Z_lt_ge_dec i left) as [Hileft | Hlefti].
- apply (H10 i j); lia.
- apply (H11 i j); lia.
```

- Result: `two_sum_sorted_proof_manual.v` compiled, contains no `Admitted.`, and contains no local `Axiom`.

## Compile command typo in one replay

- Phenomenon: one compile replay failed before checking the proof:

```text
Warning: Cannot open compcert.lib
Error: Cannot load compcert.lib.Coqlib: no physical path bound to compcert.lib
```

- Trigger: the shell array accidentally used `-R compcert.lib compcert.lib` instead of the documented `-R compcert_lib compcert.lib`.
- Localization: transient compile command recorded in `logs/coq_compile.log` before the final replay.
- Fix action: reran the full compile template from `QualifiedCProgramming/SeparationLogic` with the documented base load path:

```bash
-R compcert_lib compcert.lib
```

- Result: the final compile replay succeeded for `two_sum_sorted_goal.v`, `two_sum_sorted_proof_auto.v`, `two_sum_sorted_proof_manual.v`, and `two_sum_sorted_goal_check.v`.

## Final cleanup

- Phenomenon: successful Coq compilation produced `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under `coq/generated/`.
- Trigger: final compile replay.
- Localization: `output/verify_20260423_052427_two_sum_sorted/coq/generated/`.
- Fix action: removed all files under the workspace `coq/` directory whose names do not end in `.v`, and checked that workspace `input/` has no non-`.c`/non-`.v` files.
- Result: `find output/verify_20260423_052427_two_sum_sorted/coq -type f ! -name '*.v'` prints no files.
