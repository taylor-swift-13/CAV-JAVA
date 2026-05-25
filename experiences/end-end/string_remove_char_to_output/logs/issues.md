# Issues: string_remove_char_to_output

## 2026-04-23 symexec parser failure on postcondition `@pre`

- Phenomenon: after adding the first loop invariant and post-loop assertion, the first clean `symexec` run exited before VC generation. The generated files were all zero bytes:

```text
string_remove_char_to_output_goal.v 0 bytes
string_remove_char_to_output_goal_check.v 0 bytes
string_remove_char_to_output_proof_auto.v 0 bytes
string_remove_char_to_output_proof_manual.v 0 bytes
```

- Triggering command: local `symexec` was run against the active annotated file with `--input-file=annotated/verify_20260423_032238_string_remove_char_to_output.c`, generated-file targets under the current workspace, `--coq-logic-path=SimpleC.EE.CAV.verify_20260423_032238_string_remove_char_to_output`, and `-slp QualifiedCProgramming/QCP_examples/ SimpleC.EE`.

- Diagnostic from `logs/qcp_run.log`:

```text
fatal error: Expected C expression in annotated/verify_20260423_032238_string_remove_char_to_output.c:24:1
Now parsing : n with type :2
```

- Localization: the parser reached the function-body boundary immediately after the `Ensure`, whose active-copy postcondition still used `c@pre` and `n@pre` inside recursive list and `CharArray::full` expressions:

```c
Ensure
  exists t,
    __return == Zlength(string_remove_char_to_output_spec(l, c@pre)) &&
    Zlength(t) == n@pre - Zlength(string_remove_char_to_output_spec(l, c@pre)) &&
    CharArray::full(s, n@pre + 1, app(l, cons(0, nil))) *
    CharArray::full(out, n@pre + 1,
      app(app(string_remove_char_to_output_spec(l, c@pre), cons(0, nil)), t))
```

- Fix action: kept `input/string_remove_char_to_output.c` and `original/string_remove_char_to_output.c` unchanged, and normalized only the active annotated verification copy to the same parser-stable shape used by the local `string_copy_prefix` annotated precedent: replace `c@pre` with `c` and `n@pre` with `n` in the postcondition. This is semantically equivalent for this Verify run because the code never assigns to `c` or the ghost `n`, and the loop invariant/post-loop assertion explicitly preserve `c == c@pre`.

```c
Ensure
  exists t,
    __return == Zlength(string_remove_char_to_output_spec(l, c)) &&
    Zlength(t) == n - Zlength(string_remove_char_to_output_spec(l, c)) &&
    CharArray::full(s, n + 1, app(l, cons(0, nil))) *
    CharArray::full(out, n + 1,
      app(app(string_remove_char_to_output_spec(l, c), cons(0, nil)), t))
```

- Result: the next clean `symexec` run completed successfully:

```text
End of symbolic execution of function string_remove_char_to_output
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-23 manual proof obligations after successful symexec

- Phenomenon: fresh `coq/generated/string_remove_char_to_output_proof_manual.v` contained five generated `Admitted.` placeholders:

```text
proof_of_string_remove_char_to_output_entail_wit_1
proof_of_string_remove_char_to_output_entail_wit_2_1
proof_of_string_remove_char_to_output_entail_wit_2_2
proof_of_string_remove_char_to_output_entail_wit_3
proof_of_string_remove_char_to_output_return_wit_1
```

- Localization: the corresponding VCs are in `coq/generated/string_remove_char_to_output_goal.v`. The branch obligations require list/spec append reasoning around `string_remove_char_to_output_spec(l1 ++ [x], c_pre)`, output heap normalization after `replace_Znth j ...`, and the standard string-scan exit proof that `s[i] == 0` plus the no-internal-zero contract implies `i == n`.

- Fix action: added local helper lemmas to `coq/generated/string_remove_char_to_output_proof_manual.v`:

```coq
Lemma string_remove_char_to_output_spec_app : ...
Lemma string_remove_char_to_output_spec_keep_single : ...
Lemma string_remove_char_to_output_spec_drop_single : ...
Lemma string_remove_char_to_output_spec_zlength_le : ...
Lemma current_head_after_prefix : ...
Lemma replace_at_prefix_end : ...
```

The witness proofs instantiate loop invariant existentials with `l1 = nil` at initialization, `l1_2 ++ [x]` after each continuing iteration, split the output suffix before writes, and use `entailer!`/`lia` after rewriting the relevant list equalities.

- Result: `proof_manual.v` compiled successfully and `rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/string_remove_char_to_output_proof_manual.v` returned no matches.

## 2026-04-23 final compile and cleanup

- Phenomenon: the completed proof needed the full Coq replay, not just `proof_manual.v`, because final success requires `goal_check.v` to compile in the current workspace logic path.

- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled the task-specific original definition and generated files with the documented load-path template:

```text
original_ok
goal_ok
proof_auto_ok
proof_manual_ok
goal_check_ok
```

- Cleanup action: deleted all non-`.v` files under `output/verify_20260423_032238_string_remove_char_to_output/coq/` and deleted the generated `input/.string_remove_char_to_output.aux` file. Final checks found no remaining non-`.v` files under workspace `coq/` and no non-`.c`/non-`.v` files under `input/`.

- Result: verification succeeded in the existing workspace. `goal_check.v` compiles, `proof_manual.v` contains no `Admitted.` and no added `Axiom`, and generated intermediate artifacts were cleaned.
