# Issues

## Issue 1: input contract is rejected by `symexec` before verification can enter the function

- Phenomenon: after adding a loop invariant to the active annotated file, `symexec` failed before VC generation with:

```text
fatal error: Expected C expression in annotated/verify_20260423_033114_string_replace_char.c:23:1
Now parsing : n with type :2
```

- Trigger command:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --goal-file=output/verify_20260423_033114_string_replace_char/coq/generated/string_replace_char_goal.v \
  --proof-auto-file=output/verify_20260423_033114_string_replace_char/coq/generated/string_replace_char_proof_auto.v \
  --proof-manual-file=output/verify_20260423_033114_string_replace_char/coq/generated/string_replace_char_proof_manual.v \
  --goal-check-file=output/verify_20260423_033114_string_replace_char/coq/generated/string_replace_char_goal_check.v \
  --input-file=annotated/verify_20260423_033114_string_replace_char.c \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260423_033114_string_replace_char \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --no-exec-info
```

- Localization: the active annotated file reports the opening function body line because the parser has just finished reading the contract. The relevant formal input contract fragment is:

```c
void string_replace_char(char *s, char old_c, char new_c)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      new_c != 0 &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      exists lr,
        Zlength(lr) == n@pre &&
        ...
        CharArray::full(s, n@pre + 1, app(lr, cons(0, nil)))
*/
```

- Root cause: `n` is a ghost variable introduced by `With l n`; it is not a C parameter or local variable. A direct probe against the formal input file, before considering any loop invariant, fails with the same parser error:

```text
status:1
fatal error: Expected C expression in input/string_replace_char.c:23:1
Now parsing : n with type :2
```

This strongly indicates that the `Ensure` clauses using `n@pre` are not accepted by the front end for a ghost `With` variable. Nearby string examples use the ghost `n` directly in postconditions rather than `n@pre`.

- Fix attempted inside Verify: I first added a prefix/suffix invariant for the in-place replacement loop. The first invariant used `app(l, cons(0, nil))[i + t]`, which also produced a parser error. I rewrote that suffix expression into separate payload and terminator facts:

```c
(forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == l[i + t]) &&
l2[n@pre - i] == 0
```

The parser error persisted even when probing the original input contract, so the invariant expression was not the remaining blocker.

- Required next action: this must go back to Contract or an explicitly authorized input-spec repair. The likely contract-side repair is to replace ghost-state uses like `n@pre` with `n` in the `Ensure`, or make the length a real C parameter if `@pre` is required. Verify did not modify `input/string_replace_char.c` or the formal contract.

- Result: verification cannot proceed in this workspace under the Verify permissions. `symexec` did not produce usable VC files, no manual proof was started, and the zero-byte generated/probe files from failed parser runs were removed.

## Issue 2: retry repaired active annotated ghost `n@pre` syntax and completed VC generation

- Phenomenon: the retry inherited the same parser blocker from `logs/qcp_run.log`:

```text
fatal error: Expected C expression in annotated/verify_20260423_033114_string_replace_char.c:23:1
Now parsing : n with type :2
```

- Root cause: `n` is a `With l n` ghost variable, not a C value. The active annotated postcondition and loop invariant used `n@pre`, which the front end does not parse for ghost variables.
- Repair: in `annotated/verify_20260423_033114_string_replace_char.c`, replaced ghost length occurrences like `Zlength(lr) == n@pre`, `i <= n@pre`, and `CharArray::full(s, n@pre + 1, ...)` with direct `n`. Real C pre-state values such as `old_c@pre`, `new_c@pre`, and `s@pre` were preserved.
- Result: rerunning `symexec` on the active annotated file succeeded:

```text
Symbolic Execution into function string_replace_char
End of symbolic execution of function string_replace_char
Successfully finished symbolic execution
symexec_status: 0
```

## Issue 3: manual prefix/suffix proofs needed explicit list-shape helpers

- Phenomenon: after successful VC generation, `coq/generated/string_replace_char_proof_manual.v` contained four manual witnesses:

```coq
proof_of_string_replace_char_entail_wit_1
proof_of_string_replace_char_entail_wit_2_1
proof_of_string_replace_char_entail_wit_2_2
proof_of_string_replace_char_return_wit_1
```

- Root cause: the witnesses require normalizing `Znth` at a prefix boundary, `replace_Znth` at the first suffix cell, and the one-cell terminator suffix on loop exit. Plain `entailer!` did not infer these list equalities.
- Repair: added local helper lemmas `current_head_after_prefix`, `replace_at_prefix_end`, and `Znth_cons_succ` to `string_replace_char_proof_manual.v`. The branch witnesses destruct the suffix as `x :: xs`, rebuild the processed prefix as `l1_2 ++ new_c_pre :: nil` or `l1_2 ++ x :: nil`, and use the suffix relation at offset `0` to connect `x` with the original payload `l[i]`.
- Result: the full Coq compile template succeeded for:

```text
string_replace_char_goal.v
string_replace_char_proof_auto.v
string_replace_char_proof_manual.v
string_replace_char_goal_check.v
```

`proof_manual.v` has no `Admitted.` and no local `Axiom` declaration.
