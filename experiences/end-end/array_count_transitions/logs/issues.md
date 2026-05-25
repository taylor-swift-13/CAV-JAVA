# Verification Issues

## Fingerprint Completion

- Phenomenon: `logs/workspace_fingerprint.json` initially contained an empty `semantic_description` and `{}` keywords.
- Trigger: the verify workspace was bootstrapped before task-specific semantic classification.
- Localization: `output/verify_20260422_033321_array_count_transitions/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled in a concrete semantic description for a read-only adjacent-transition array scan and used only controlled vocabulary keys/values: `counting`, `for_loop`, `array`, `preserve_input`, `loop_invariant`, `case_split`, `range_bound`, `heap_reasoning`, `nonnegative_input`, `int_range`, `monotone_accumulator`, `empty_loop_possible`.
- Result: the fingerprint is non-empty and now records `verification_status: goal_check_passed`.

## Missing Loop Invariant

- Phenomenon: the active annotated copy initially had no invariant for:

```c
for (i = 1; i < n; ++i) {
    if (a[i] != a[i - 1]) {
        cnt++;
    }
}
```

- Trigger: the postcondition requires `__return == array_count_transitions_spec(l)`, but without a loop-head invariant symbolic execution has no stable relation between `cnt` and the already processed adjacent pairs.
- Localization: `annotated/verify_20260422_033321_array_count_transitions.c`.
- Fix action: appended detailed reasoning to `logs/annotation_reasoning.md` and added this invariant immediately before the `for` loop:

```c
/*@ Inv
      1 <= i && i <= n + 1 &&
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_transitions_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

- Result: the invariant handles the `n == 0` skip-loop case because `i` starts at `1`, preserves the read-only array resource, and gives proof obligations for prefix extension.

## First Symexec Invocation Used Split Flags

- Phenomenon: the first manual symexec probe wrote only:

```text
goal file not specified
Start to symbolic execution on program : (null)
```

- Trigger: the local `QualifiedCProgramming/linux-binary/symexec` binary expects output/input flags in `--flag=value` form; the split form `--goal-file path` leaves the goal and input unset.
- Localization: preserved failed probe in `logs/qcp_run.raw`; final successful run is in `logs/qcp_run.log`.
- Fix action: reran `symexec` with `--goal-file=...`, `--proof-auto-file=...`, `--proof-manual-file=...`, `--goal-check-file=...`, and `--input-file=...`.
- Result: the corrected invocation reached the annotated function body.

## Exit Assertion Interfered With Local Cleanup

- Phenomenon: after adding the first loop invariant plus a post-loop assertion, `symexec` failed at the final return with:

```text
fatal error: Error: Fail to Remove Memory Permission of i:95 in
annotated/verify_20260422_033321_array_count_transitions.c:42:4
Address found : null
```

- Trigger: the extra assertion was placed immediately before `return cnt;`:

```c
/*@ Assert
      a == a@pre &&
      n == n@pre &&
      cnt == array_count_transitions_spec(l) &&
      IntArray::full(a, n, l)
*/
return cnt;
```

- Diagnosis: this matched the known assertion-placement failure mode where a loop-exit assertion too close to return/local cleanup interferes with removing local variable permissions, here for `i`.
- Fix action: removed the post-loop assertion and kept the loop invariant unchanged. The return relation was left as a generated Coq witness.
- Result: the next clean `symexec` run completed successfully and generated fresh `array_count_transitions_goal.v`, `array_count_transitions_proof_auto.v`, `array_count_transitions_proof_manual.v`, and `array_count_transitions_goal_check.v`.

## Manual Proof Obligations

- Phenomenon: successful `symexec` generated five admitted manual obligations in `coq/generated/array_count_transitions_proof_manual.v`:

```coq
proof_of_array_count_transitions_safety_wit_5
proof_of_array_count_transitions_entail_wit_1
proof_of_array_count_transitions_entail_wit_2_1
proof_of_array_count_transitions_entail_wit_2_2
proof_of_array_count_transitions_return_wit_1
```

- Trigger: the verification conditions needed pure Coq facts for adjacent-transition prefix extension, nonnegative/range bounds for `cnt + 1`, singleton-prefix initialization, and full-prefix normalization at return.
- Localization: `output/verify_20260422_033321_array_count_transitions/coq/generated/array_count_transitions_proof_manual.v`.
- Fix action: added local helper lemmas for `sublist_prefix_full`, `sublist_prefix_snoc_Z`, `last_sublist_prefix_Z`, transition-spec snoc extension, nonempty-prefix facts, prefix-step rewriting, and transition-count bounds. Then replaced all five `Admitted.` bodies with concrete proofs.
- Result: `rg -n "Admitted\\.|^Axiom\\b" coq/generated/array_count_transitions_proof_manual.v` returns no matches.

## Proof Iteration Details

- Phenomenon: the first compile replay after adding helper lemmas failed before witness proofs with:

```text
Error: Found no subterm matching "Zlength nil" in the current goal.
```

- Localization: `array_count_transitions_proof_manual.v`, helper lemma `array_count_transitions_spec_bounds`.
- Fix action: replaced the nil branch `simpl. rewrite Zlength_nil. lia.` with `simpl. lia.` because simplification had already removed the literal `Zlength nil` subterm.
- Result: compilation advanced to the initialization witness.

- Phenomenon: the initialization witness then failed with `Cannot find witness` when the script tried to solve a sublist-prefix semantic goal by length arithmetic.
- Localization: `proof_of_array_count_transitions_entail_wit_1`.
- Fix action: simplified the proof to destruct `l`; both the empty and nonempty cases reduce to `reflexivity` after `entailer!`, because `sublist 0 1 l` is empty or a singleton and both have transition count zero.
- Result: the manual proof file compiled.

## Compile Replay And Cleanup

- Phenomenon: final verification requires compiling the optional spec file and all generated Coq files with the workspace logical path, then cleaning generated binary artifacts.
- Trigger: verify completion criteria require `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile, and `coq/` to contain no non-`.v` intermediates.
- Localization: `logs/compile.log` and `output/verify_20260422_033321_array_count_transitions/coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` using the documented `BASE` load path, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_033321_array_count_transitions`; then deleted `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/`.
- Result: `original/array_count_transitions.v`, `array_count_transitions_goal.v`, `array_count_transitions_proof_auto.v`, `array_count_transitions_proof_manual.v`, and `array_count_transitions_goal_check.v` all compiled successfully. After cleanup, only the four generated `.v` files remain under `coq/generated/`.
