# Verification Issues

## 2026-04-23 fingerprint initialized from controlled retrieval vocabulary

- Phenomenon: the workspace was initialized with an empty `semantic_description` and empty `keywords` in `logs/workspace_fingerprint.json`, which violates the Verify workflow requirement for retrieval-ready fingerprints.
- Triggering file:

```json
"semantic_description": "",
"keywords": {}
```

- Localization: `output/verify_20260423_044748_string_to_upper_ascii/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a non-empty description of the in-place null-terminated string uppercase conversion. Keywords use only controlled values: `simulation`, `while_loop`, `if`, `string`, `array`, `pointer`, `in_place_update`, `loop_invariant`, `case_split`, `range_bound`, `heap_reasoning`, `overflow_guard`, `int_range`, `empty_loop_possible`, and after successful verification `manual_witness_needed`, `goal_check_passed`, `proof_check_passed`.
- Result: the fingerprint is now non-empty and retrieval-compatible.

## 2026-04-23 loop invariant required for in-place string update

- Phenomenon: the active annotated C initially matched `input/string_to_upper_ascii.c` and had no `Inv` before the `while (1)` scan. Without an invariant, `symexec` would not have a stable loop-head assertion describing the transformed prefix, the still-original suffix, the zero terminator, or the buffer ownership needed by the postcondition.
- Triggering code:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] >= 97 && s[i] <= 122) {
        s[i] = s[i] - 32;
    }
    i++;
}
```

- Localization: `annotated/verify_20260423_044748_string_to_upper_ascii.c`, immediately before the `while (1)` loop.
- Fix action: added a prefix/suffix invariant with existential lists `l1` and `l2`:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      s == s@pre &&
      n == Zlength(l) &&
      Zlength(l1) == i &&
      Zlength(l2) == n + 1 - i &&
      (forall (t: Z), (0 <= t && t < i && 97 <= l[t] && l[t] <= 122) => l1[t] == l[t] - 32) &&
      (forall (t: Z), (0 <= t && t < i && (l[t] < 97 || 122 < l[t])) => l1[t] == l[t]) &&
      (forall (t: Z), (0 <= t && t < i) => l1[t] != 0) &&
      (forall (t: Z), (0 <= t && t < n - i) => l2[t] == l[i + t]) &&
      l2[n - i] == 0 &&
      CharArray::full(s, n + 1, app(l1, l2))
*/
```

- Why this fixes the issue: `l1` represents the already-uppercased prefix, `l2` represents the original unprocessed suffix plus terminator, `i` is the processed-prefix length, and the heap predicate `CharArray::full(s, n + 1, app(l1, l2))` tracks the in-place updates across loop iterations. At loop exit, the zero read plus the precondition that all payload characters are nonzero identifies `i == n`, letting the postcondition choose `lr = l1`.
- Result: after the parser repair below, `symexec` accepted this invariant and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## 2026-04-23 parser repair for ghost `With` variable `n@pre`

- Phenomenon: the active annotated postcondition used `n@pre` even though `n` is introduced by `With l n`, not by a C parameter or local declaration. The same shape is documented in the verified lowercase counterpart as a parser failure. To avoid that front-end issue before running `symexec`, the active annotated verification copy was repaired.
- Triggering annotated fragment:

```c
Ensure
  exists lr,
    Zlength(lr) == n@pre &&
    (forall (i: Z), (0 <= i && i < n@pre) => ...) &&
    (forall (k: Z), (0 <= k && k < n@pre) => lr[k] != 0) &&
    CharArray::full(s, n@pre + 1, app(lr, cons(0, nil)))
```

- Localization: `annotated/verify_20260423_044748_string_to_upper_ascii.c`, function contract `Ensure`.
- Fix action: changed only the active annotated verification copy, replacing those ghost-length occurrences with direct `n`. The formal input file under `input/` was not modified.
- Result: the clean `symexec` run completed successfully:

```text
symexec_start=2026-04-23 04:49:45 +0800
Symbolic Execution into function string_to_upper_ascii
End of symbolic execution of function string_to_upper_ascii
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-23 manual proof obligation for invariant initialization

- Phenomenon: after successful `symexec`, `coq/generated/string_to_upper_ascii_proof_manual.v` contained one admitted manual obligation:

```coq
Lemma proof_of_string_to_upper_ascii_entail_wit_1 : string_to_upper_ascii_entail_wit_1.
Proof. Admitted.
```

- Localization: `string_to_upper_ascii_entail_wit_1` in `coq/generated/string_to_upper_ascii_goal.v` is the loop-invariant initialization entailment from the original heap `CharArray.full s_pre (n + 1) (app l (cons 0 nil))` to the invariant with existential `l1` and `l2`.
- Fix action: chose `l1 = nil` and `l2 = l ++ 0 :: nil`, then discharged the pure suffix and length goals using `app_Znth1`, `app_Znth2`, `Zlength_app`, `Zlength_cons`, `Zlength_nil`, and `lia`:

```coq
Proof.
  pre_process.
  Exists (l ++ 0 :: nil) (@nil Z).
  entailer!.
  - replace (n - 0) with (Zlength l) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength l - Zlength l) with 0 by lia.
    simpl. reflexivity.
  - intros t Ht.
    replace (0 + t) with t by lia.
    rewrite app_Znth1 by lia.
    reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.
```

- Result: `proof_manual.v` compiles and `rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/string_to_upper_ascii_proof_manual.v` finds no forbidden lines.

## 2026-04-23 final compile and cleanup

- Phenomenon: successful `symexec` and manual proof compilation are not sufficient; the verify workflow requires compiling `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, then deleting non-`.v` Coq intermediates under the current workspace.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` paths plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260423_044748_string_to_upper_ascii`.
- Result from `logs/coq_compile.log`:

```text
goal: ok
proof_auto: ok
proof_manual: ok
goal_check: ok
```

- Cleanup result: removed generated `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under `output/verify_20260423_044748_string_to_upper_ascii/coq/`. No workspace `input/` directory existed, and `find output/verify_20260423_044748_string_to_upper_ascii/coq -type f ! -name '*.v'` returns no files.
