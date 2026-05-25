# Verification Issues

## Missing loop invariant in active annotated C

- Phenomenon: the active annotated copy initially matched the input implementation and had a bare `while (1)` loop:

```c
int i = 0;
int cnt = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == 32) {
        cnt++;
    }
    i++;
}
```

- Trigger: `string_count_spaces` is a string scan whose postcondition needs `__return == string_count_spaces_spec(l)`. Without a loop invariant, symbolic execution has no reusable state connecting `cnt` to the already processed prefix or preserving the `CharArray::full` resource.
- Localization: `annotated/verify_20260423_011517_string_count_spaces.c`, before the single `while (1)` loop.
- Fix action: added a prefix-count invariant that tracks `l == app(l1, l2)`, `Zlength(l1) == i`, `cnt == string_count_spaces_spec(l1)`, the nonzero-prefix contract fact, `s == s@pre`, bounds for `i` and `cnt`, and the preserved `CharArray::full` resource. Added a loop-exit assertion immediately after the loop to pin `i == n`, `cnt == string_count_spaces_spec(l)`, and the preserved resource before `return cnt`.
- Result: after clearing stale generated targets, `QualifiedCProgramming/linux-binary/symexec` completed successfully on the current annotated file. `logs/qcp_run.log` ended with:

```text
Symbolic Execution into function string_count_spaces
End of symbolic execution of function string_count_spaces
Successfully finished symbolic execution
```

## Manual witnesses required a one-element append helper

- Phenomenon: after successful symbolic execution, `coq/generated/string_count_spaces_proof_manual.v` contained four generated `Admitted.` placeholders:

```coq
Lemma proof_of_string_count_spaces_entail_wit_1 : string_count_spaces_entail_wit_1.
Lemma proof_of_string_count_spaces_entail_wit_2_1 : string_count_spaces_entail_wit_2_1.
Lemma proof_of_string_count_spaces_entail_wit_2_2 : string_count_spaces_entail_wit_2_2.
Lemma proof_of_string_count_spaces_entail_wit_3 : string_count_spaces_entail_wit_3.
```

- Trigger: the loop-preservation witnesses need to relate the old processed-prefix count to the count after appending the current character. In the `s[i] == 32` branch, the new count is `cnt + 1`; in the `s[i] != 32` branch, the count remains `cnt`.
- Localization: `coq/generated/string_count_spaces_goal.v`, definitions `string_count_spaces_entail_wit_2_1` and `string_count_spaces_entail_wit_2_2`.
- Fix action: added the local helper:

```coq
Lemma string_count_spaces_spec_app_single :
  forall (l : list Z) (x : Z),
    string_count_spaces_spec (l ++ x :: nil) =
    string_count_spaces_spec l + (if Z.eq_dec x 32 then 1 else 0).
```

Then proved the two preservation witnesses by decomposing the remaining suffix into `x :: xs`, extracting either `x = 32` or `x <> 32` from the branch condition, choosing witnesses `l1_2 ++ x :: nil` and `xs`, and letting `entailer!` close the separation and arithmetic residue.
- Result: the manual proof file now contains no `Admitted.` and no new `Axiom`; it compiled successfully.

## Proof script initially matched a brittle `Znth` term shape

- Phenomenon: the first `coqc` attempt after replacing manual stubs failed in `proof_of_string_count_spaces_entail_wit_2_1`:

```text
File ".../string_count_spaces_proof_manual.v", line 75, characters 4-282:
Error: No matching clauses for match.
```

The failing code matched a fully parenthesized expression:

```coq
match goal with
| Hnz : Znth i (l1_2 ++ nil ++ 0 :: nil) 0 <> 0 |- _ => ...
end
```

- Trigger: after `pre_process` and `subst l`, the proof state contained the right nonzero hypothesis, but its list expression was parenthesized differently from the match pattern.
- Localization: `coq/generated/string_count_spaces_proof_manual.v`, empty-suffix case in `proof_of_string_count_spaces_entail_wit_2_1`; the same brittle pattern existed in `proof_of_string_count_spaces_entail_wit_2_2`.
- Fix action: rewrote the proof to follow the already compiled `string_count_digits` proof style. It uses the stable generated hypothesis order directly: `H` for the branch predicate and `H0` for the nonzero read in these two witnesses. The impossible empty-suffix case now rewrites `H0`; the nonempty case rewrites `H` to extract the current character fact.
- Result: the next full compile chain succeeded for `original/string_count_spaces.v`, `string_count_spaces_goal.v`, `string_count_spaces_proof_auto.v`, `string_count_spaces_proof_manual.v`, and `string_count_spaces_goal_check.v`.

## Cleanup after successful compile

- Phenomenon: compiling generated Coq files produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` intermediate artifacts under `coq/generated/`.
- Trigger: normal `coqc` output from the final compile chain.
- Localization: `output/verify_20260423_011517_string_count_spaces/coq/generated/`.
- Fix action: deleted all non-`.v` files under the current workspace `coq/` tree after the successful compile. Checked `./input` and found no non-`.c`/non-`.v` intermediate files to remove.
- Result: the workspace `coq/` tree now contains only:

```text
generated/string_count_spaces_goal.v
generated/string_count_spaces_goal_check.v
generated/string_count_spaces_proof_auto.v
generated/string_count_spaces_proof_manual.v
```
