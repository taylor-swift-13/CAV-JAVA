# Issues

## Missing loop invariant in the active annotated C

- Phenomenon: the active annotated file initially copied the input implementation and had no `Inv` before the `while (1)` scan loop. Without a loop summary, symexec would not have the persistent relation between `cnt`, `i`, the processed string prefix, and the preserved `CharArray::full` resource needed for the return proof.
- Trigger: the target function scans a null-terminated string, branches on digit range, increments `cnt`, and returns after seeing the sentinel:

```c
while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] >= 48 && s[i] <= 57) {
        cnt++;
    }
    i++;
}
```

- Fix action: added an invariant in `annotated/verify_20260423_003638_string_count_digits.c` splitting `l = app(l1, l2)`, keeping `Zlength(l1) == i`, `cnt == string_count_digits_spec(l1)`, `0 <= cnt <= i`, `s == s@pre`, the nonzero-prefix fact, and `CharArray::full(s, n + 1, app(l, cons(0, nil)))`. Added a post-loop assertion fixing `i == n`, `cnt == string_count_digits_spec(l)`, and the preserved heap resource.
- Result: after clearing stale generated files, symexec completed successfully and generated fresh `string_count_digits_goal.v`, `string_count_digits_proof_auto.v`, `string_count_digits_proof_manual.v`, and `string_count_digits_goal_check.v`. `logs/qcp_run.log` ends with:

```text
End of symbolic execution of function string_count_digits
Successfully finished symbolic execution
symexec_status=0
```

## Manual proof required prefix-extension list reasoning

- Phenomenon: fresh `string_count_digits_proof_manual.v` contained five generated `Admitted.` placeholders:

```coq
proof_of_string_count_digits_entail_wit_1
proof_of_string_count_digits_entail_wit_2_1
proof_of_string_count_digits_entail_wit_2_2
proof_of_string_count_digits_entail_wit_2_3
proof_of_string_count_digits_entail_wit_3
```

- Trigger: these obligations are pure list/arithmetic witnesses for initializing the invariant, preserving it across digit and non-digit branches, and converting a sentinel read into `i = n` at loop exit. The key missing theorem was the append-last behavior of `string_count_digits_spec`.
- Fix action: added local helper lemma `string_count_digits_spec_app_single` to `coq/generated/string_count_digits_proof_manual.v`, then proved the five witnesses. The branch proofs expose the next character by destructing `l2_2`, use witnesses `l1_2 ++ x :: nil` and `xs`, and prove the spec update by case-splitting on `Z_le_dec 48 x` and `Z_le_dec x 57`.
- Result: all manual witnesses are proven. `string_count_digits_proof_manual.v` contains no `Admitted.` and no new `Axiom`.

## Brittle proof pattern after `subst i` in branch contradiction

- Phenomenon: the first manual compile attempt failed at line 68 of `string_count_digits_proof_manual.v` with:

```text
Error: No matching clauses for match.
```

- Trigger: the proof tried to match `Hnz : Znth n (l ++ 0 :: nil) 0 <> 0` after `subst i`. Coq rewrote `i` through `Zlength l1_2`, leaving a hypothesis shaped like `Znth (Zlength l1_2) (l ++ 0 :: nil) 0 <> 0`, so the exact match failed.
- Fix action: stopped using dependent `subst i` in the contradiction blocks. Instead, derived `Hi_eq : i = n`, rewrote the concrete nonzero branch hypothesis with `Hi_eq`, and then rewrote `app_Znth2` using `Hlen_l : Zlength l = n`.
- Result: the sentinel contradiction blocks became stable in all three branch-preservation witnesses.

## `Znth 0` over an exposed cons did not simplify for arithmetic

- Phenomenon: after the contradiction fix, compile failed at line 92 with:

```text
Error: Tactic failure: Cannot find witness.
```

- Trigger: after exposing the current character, the proof state had goals such as `48 <= x`, while the branch hypothesis remained:

```coq
H0 : Znth 0 (x :: xs ++ 0 :: nil) 0 >= 48
```

`simpl in H0` did not reduce this `Znth 0` expression to `x`, so `lia` could not use it directly.
- Fix action: added explicit conversions after the prefix-access rewrite:

```coq
change (Znth 0 (x :: xs ++ 0 :: nil) 0) with x in H0.
```

and the corresponding conversions for the `<= 57`, `< 48`, and `> 57` branch hypotheses.
- Result: arithmetic case splits for digit and non-digit branches compiled.

## Prefix-extension witnesses needed explicit append and length bridge facts

- Phenomenon: after the `Znth 0` conversions, `proof_of_string_count_digits_entail_wit_2_1` reached `entailer!` but failed at `Qed` with:

```text
Attempt to save an incomplete proof
(there are remaining open goals).
```

- Trigger: the chosen witnesses were `l1_2 ++ x :: nil` and `xs`, but `entailer!` needed explicit pure facts connecting the original list decomposition and new prefix length:

```coq
l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs
Zlength (l1_2 ++ x :: nil) = i + 1
```

- Fix action: added `Happ` and `Hlen_prefix` before `Exists` in all three prefix-extension witnesses.
- Result: the final compile replay succeeded through `string_count_digits_goal_check.v`.

## Final compile and cleanup

- Phenomenon: verification is not complete after symexec or isolated manual proof compilation; the full chain and cleanup are required.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` paths, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260423_003638_string_count_digits`. Then removed non-`.v` Coq intermediates from the workspace `coq/` tree. `input/` had no non-`.c`/non-`.v` intermediates.
- Result: `logs/compile.log` records:

```text
compiled string_count_digits.v
compiled string_count_digits_goal.v
compiled string_count_digits_proof_auto.v
compiled string_count_digits_proof_manual.v
compiled string_count_digits_goal_check.v
```

After cleanup, `find output/verify_20260423_003638_string_count_digits/coq -type f ! -name '*.v'` produced no output.
