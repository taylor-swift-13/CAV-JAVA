# Verify Issues

## 2026-04-22 18:43 - Fingerprint placeholder had to be filled

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and `{}` keywords.
- Trigger: the verify workspace was initialized before semantic analysis.
- Location: `output/verify_20260422_184334_longest_increasing_run/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled the fingerprint with a concrete description of the read-only array scan and used only controlled-vocabulary keys and values:

```json
"algorithm_family": ["search", "accumulation"],
"control_flow": ["if", "for_loop"],
"data_shape": "array",
"semantic_intent": ["return_max", "preserve_input"],
"proof_pattern": ["loop_invariant", "case_split", "range_bound"],
"numeric_properties": ["nonnegative_input", "int_range", "monotone_accumulator"],
"edge_case_behavior": ["empty_loop_possible", "branch_on_order"]
```

- Result: the fingerprint is non-empty and later records verification status values `goal_check_passed`, `proof_check_passed`, `manual_witness_needed`, and `generated_goal_contains_axioms`.

## 2026-04-22 18:43 - Active annotated C lacked the required accumulator loop invariant

- Phenomenon: the active annotated file initially copied the input contract and implementation but had no `Inv` before the loop:

```c
cur = 1;
best = 1;
for (i = 1; i < n; ++i) {
    if (a[i - 1] < a[i]) {
        cur++;
    } else {
        cur = 1;
    }
    if (best < cur) {
        best = cur;
    }
}
```

- Trigger: the postcondition requires `__return == longest_increasing_run_spec(l)` and preservation of `IntArray::full(a, n, l)`. Without an invariant, symbolic execution has no durable relation between `cur`, `best`, the processed prefix, and the unprocessed suffix.
- Location: `annotated/verify_20260422_184334_longest_increasing_run.c`.
- Fix action: appended detailed reasoning to `logs/annotation_reasoning.md`, exposed the existing Coq helper, and added a loop-head invariant:

```c
/*@ Extern Coq (longest_increasing_run_acc : Z -> Z -> Z -> list Z -> Z) */

/*@ Inv
      1 <= i && i <= n &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      1 <= cur && cur <= i &&
      1 <= best && best <= i &&
      longest_increasing_run_acc(Znth(i - 1, l, 0), cur, best, sublist(i, n, l)) ==
        longest_increasing_run_spec(l) &&
      IntArray::full(a, n, l)
*/
```

- Result: the final `symexec` pass used this invariant and generated the expected witness definitions for initialization, three loop-preservation branches, and two return paths.

## 2026-04-22 18:46 - Incorrect `symexec` input flag attempted to parse the optional Coq file as C

- Phenomenon: the first manual `symexec` command failed immediately with:

```text
fatal error: bison: syntax error, unexpected PT_IDENT, expecting PT_SEMI in input/longest_increasing_run.v:1:14
Start to symbolic execution on program : input/longest_increasing_run.v
```

- Trigger: `--input-file` was incorrectly pointed at `input/longest_increasing_run.v`. For this binary, `--input-file` is the annotated C program input, not the companion Coq spec.
- Location: terminal run before the final `logs/qcp_run.log`.
- Fix action: reran `symexec` with `--input-file=annotated/verify_20260422_184334_longest_increasing_run.c` and explicit generated output paths.
- Result: the command-line role was corrected. A later run after restoring the annotated file successfully entered `longest_increasing_run`.

## 2026-04-22 18:47 - Empty VC generation exposed a zero-byte active annotated file

- Phenomenon: a subsequent `symexec` run returned status 0 but did not print strategy parsing lines or `Symbolic Execution into function longest_increasing_run`. The generated `longest_increasing_run_goal.v` contained an empty module:

```coq
Module Type VC_Correct.

End VC_Correct.
```

- Trigger: inspection showed `annotated/verify_20260422_184334_longest_increasing_run.c` had become a zero-byte file, so the tool had no C function to parse.
- Location: active annotated C and the generated empty `coq/generated/longest_increasing_run_goal.v`.
- Fix action: restored the active annotated C from the input implementation plus the helper declaration and the invariant. While restoring, used explicit `Znth(i - 1, l, 0)` in the invariant instead of bracket shorthand inside the imported helper call.
- Result: the next `symexec` run showed the complete expected trace:

```text
Start to parse strategies file common
...
Start to parse strategies file array_shape
Symbolic Execution into function longest_increasing_run
End of symbolic execution of function longest_increasing_run
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-22 18:50 - Manual proof obligations required local list/accumulator helpers

- Phenomenon: after successful symbolic execution, `coq/generated/longest_increasing_run_proof_manual.v` contained six admitted witnesses:

```coq
proof_of_longest_increasing_run_entail_wit_1
proof_of_longest_increasing_run_entail_wit_2_1
proof_of_longest_increasing_run_entail_wit_2_2
proof_of_longest_increasing_run_entail_wit_2_3
proof_of_longest_increasing_run_return_wit_1
proof_of_longest_increasing_run_return_wit_2
```

- Trigger: the generated VCs are pure list/arithmetic facts: initialize the accumulator invariant for a nonempty list, rewrite `sublist i n l` as a cons at each loop iteration, split on `Z_lt_dec`, normalize `Z.max`, and reduce the empty suffix at loop exit.
- Location: `output/verify_20260422_184334_longest_increasing_run/coq/generated/longest_increasing_run_proof_manual.v`.
- Fix action: appended `logs/proof_reasoning.md`, then added local helper lemmas and concrete witness proofs:

```coq
Lemma sublist_head_cons_Z : ...
Lemma longest_increasing_run_spec_nonempty_acc : ...
Lemma longest_increasing_run_acc_step : ...
```

- Result: `longest_increasing_run_proof_manual.v` compiles and `rg -n "Admitted\\.|^\\s*Axiom\\b|^\\s*Parameter\\b"` returns no matches for the manual proof file.

## 2026-04-22 18:51 - Full Coq replay and cleanup

- Phenomenon: verification is not complete until the original spec and all generated Coq files compile with the workspace load path, and build artifacts are removed afterward.
- Trigger: normal `coqc` replay creates `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Location: `logs/compile.log` and `coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented `BASE` load path, `-Q "$ORIG" ""`, and `-R "$GEN" "SimpleC.EE.CAV.verify_20260422_184334_longest_increasing_run"`. The compile log records:

```text
compiled=original/longest_increasing_run.v
compiled=coq/generated/longest_increasing_run_goal.v
compiled=coq/generated/longest_increasing_run_proof_auto.v
compiled=coq/generated/longest_increasing_run_proof_manual.v
compiled=coq/generated/longest_increasing_run_goal_check.v
compile_status=0
```

- Result: `goal_check.v` compiled successfully. All non-`.v` files under the workspace `coq/` tree were deleted, and `input/` had no non-`.c`/non-`.v` intermediate files.
