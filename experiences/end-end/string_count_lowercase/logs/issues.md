## 2026-04-23 Verify issues and fixes

### Issue 1: workspace fingerprint had empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` was still in script-initialized form with an empty `semantic_description` and `{}` keywords.
- Trigger: the verify workflow requires this file to be filled early, and keywords must use only the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Localization: `logs/workspace_fingerprint.json`.
- Fix action: after reading `doc/retrieval/INDEX.md`, filled the semantic description as a NUL-terminated string scan that counts lowercase ASCII letters while preserving the input `CharArray::full` resource. Keywords used only controlled values such as `counting`, `while_loop`, `string`, `loop_invariant`, `case_split`, `range_bound`, and later `goal_check_passed`.
- Result: fingerprint is non-empty and uses only the controlled vocabulary.

### Issue 2: active annotated C lacked a loop invariant for the string scan

- Phenomenon: the active annotated file initially copied the input C exactly and had no `Inv` before `while (1)`, so symbolic execution would not have a reusable loop summary for `i`, `cnt`, the prefix already scanned, or the preserved string buffer.
- Localization: `annotated/verify_20260423_004841_string_count_lowercase.c`.
- Key pre-fix fragment:

```c
int i = 0;
int cnt = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] >= 97 && s[i] <= 122) {
        cnt++;
    }
    i++;
}
```

- Fix action: added an `exists l1 l2` invariant following the stable `string_count_digits` and `string_count_char` examples. The invariant records `l == app(l1, l2)`, `Zlength(l1) == i`, `cnt == string_count_lowercase_spec(l1)`, `0 <= cnt && cnt <= i`, `0 <= i && i <= n`, `s == s@pre`, the nonzero-prefix property, and the unchanged `CharArray::full` ownership.
- Added invariant:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= cnt && cnt <= i &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      Zlength(l) == n &&
      cnt == string_count_lowercase_spec(l1) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Result: the invariant gives symbolic execution enough prefix semantics and overflow bounds for the loop body.

### Issue 3: loop exit needed an explicit bridge to the function postcondition

- Phenomenon: after the `break` path, the postcondition needs `cnt == string_count_lowercase_spec(l)`, but the invariant only states the prefix fact `cnt == string_count_lowercase_spec(l1)`.
- Localization: immediately after the loop in the active annotated C.
- Fix action: added a loop-exit `Assert` that records `i == n`, `Zlength(l1) == n`, and `cnt == string_count_lowercase_spec(l)` while preserving the same `CharArray::full` resource.
- Added exit assertion:

```c
/*@ Assert exists l1 l2,
      i == n &&
      0 <= cnt && cnt <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == n &&
      Zlength(l) == n &&
      cnt == string_count_lowercase_spec(l) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Result: `symexec` accepted the annotation and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

### Issue 4: manual proof contained five generated `Admitted.` entailment witnesses

- Phenomenon: after successful symbolic execution, `coq/generated/string_count_lowercase_proof_manual.v` contained five generated stubs:

```coq
proof_of_string_count_lowercase_entail_wit_1
proof_of_string_count_lowercase_entail_wit_2_1
proof_of_string_count_lowercase_entail_wit_2_2
proof_of_string_count_lowercase_entail_wit_2_3
proof_of_string_count_lowercase_entail_wit_3
```

- Localization: `coq/generated/string_count_lowercase_proof_manual.v`.
- Fix action: adapted the completed `string_count_digits` proof pattern. Added `string_count_lowercase_spec_app_single`, then proved each witness by splitting the current suffix into `x :: xs`, using lowercase branch facts (`97 <= x <= 122`, `x < 97`, or `x > 122`), advancing the prefix to `l1_2 ++ x :: nil`, and using `CharArray.full_length` plus the nonzero-prefix precondition to prove the exit fact `i = n`.
- Key helper:

```coq
Lemma string_count_lowercase_spec_app_single :
  forall (l : list Z) (x : Z),
    string_count_lowercase_spec (l ++ x :: nil) =
    string_count_lowercase_spec l +
    (if Z_le_dec 97 x then if Z_le_dec x 122 then 1 else 0 else 0).
```

- Result: `coq/generated/string_count_lowercase_proof_manual.v` compiles and `rg -n "Admitted\\.|^\\s*Axiom\\b"` finds no forbidden lines in the manual proof file.

### Issue 5: full Coq compile replay and cleanup were required

- Phenomenon: successful `symexec` and manual proof editing are not sufficient; the workflow requires compiling `original/string_count_lowercase.v`, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, then removing compilation intermediates.
- Fix action: from `QualifiedCProgramming/SeparationLogic`, compiled with the documented base `-R` paths plus `-Q "$ORIG" ""` and `-R "$GEN" "SimpleC.EE.CAV.verify_20260423_004841_string_count_lowercase"`.
- Compile result:

```text
compiled original/string_count_lowercase.v
compiled string_count_lowercase_goal.v
compiled string_count_lowercase_proof_auto.v
compiled string_count_lowercase_proof_manual.v
compiled string_count_lowercase_goal_check.v
```

- Cleanup action: deleted non-`.v`/non-`.c` intermediates under the workspace `coq/` and `original/` directories. The project `input/` directory had no non-`.v`/non-`.c` files to remove.
- Result: `goal_check.v` compiles, the manual proof has no `Admitted.` or local `Axiom`, and the workspace source artifacts remain.
