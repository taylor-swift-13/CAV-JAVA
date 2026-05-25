# Verify Issues

## No annotation change was needed

- Phenomenon: the active annotated file `annotated/verify_20260423_042409_string_starts_with.c` matched `input/string_starts_with.c` and the function body was straight-line:

```c
if (s[0] == c) {
    return 1;
}
return 0;
```

- Reasoning: there is no loop and no intermediate mutation.  The precondition already provides the full `CharArray::full(s, n + 1, app(l, cons(0, nil)))` resource and the pure facts needed to relate `s[0]` to either `l[0]` for `0 < n` or the appended terminator for `n = 0`.
- Fix action: skipped `annotation_reasoning.md` and did not edit the active annotated C file.
- Result: `symexec` completed successfully on the unchanged annotated file.

## Manual postcondition proof required explicit four-way case selection

- Phenomenon: fresh `symexec` generated two manual return witnesses in `coq/generated/string_starts_with_proof_manual.v`:

```coq
Lemma proof_of_string_starts_with_return_wit_1 : string_starts_with_return_wit_1.
Proof. Admitted.

Lemma proof_of_string_starts_with_return_wit_2 : string_starts_with_return_wit_2.
Proof. Admitted.
```

- Trigger: both return branches must prove a four-way postcondition:

```coq
non-empty mismatch || non-empty match || empty mismatch || empty match
```

The branch condition from the C `if` is expressed as either:

```coq
Znth 0 (l ++ 0 :: nil) 0 = c_pre
```

or:

```coq
Znth 0 (l ++ 0 :: nil) 0 <> c_pre
```

- Fix action: split on `Z.eq_dec n 0`.  For `0 < n`, rewrote the appended string head with `app_Znth1` to derive `Znth 0 l 0 = c_pre` or `Znth 0 l 0 <> c_pre`.  For `n = 0`, rewrote with `app_Znth2`, normalized `0 - Zlength l` to `0`, and reduced the singleton terminator access to derive `c_pre = 0` or `c_pre <> 0`.
- Result: both manual witnesses were completed without `Admitted.`, `admit.`, or a local `Axiom`.

## First proof compile failed because the disjunction was left-associated

- Phenomenon: the first compile replay failed while compiling `string_starts_with_proof_manual.v`:

```text
File ".../string_starts_with_proof_manual.v", line 28, characters 4-9:
Error: Found no subterm matching "?e || ?e0" in the current goal.
```

- Cause: the generated four-way postcondition is parsed as `(((A || B) || C) || D)`.  The initial script used too many `Right` tactics for the fourth disjunct:

```coq
Right.
Right.
Right.
```

After the first `Right`, the fourth disjunct had already been selected and no `||` remained.
- Fix action: changed disjunct navigation to the left-associated shape:

```coq
(* A *) Left. Left. Left.
(* B *) Left. Left. Right.
(* C *) Left. Right.
(* D *) Right.
```

- Result: the disjunction navigation error disappeared in the next compile attempt.

## Second proof compile needed pure facts before `entailer!`

- Phenomenon: the next compile replay failed at the empty `return_wit_1` branch:

```text
File ".../string_starts_with_proof_manual.v", line 31, characters 6-9:
Error: Tactic failure:  Cannot find witness.
```

- Cause: the script selected the right disjunct and called `entailer!` before exposing the pure fact `c_pre = 0`; that fact was still hidden inside `H : Znth 0 (l ++ 0 :: nil) 0 = c_pre`.
- Fix action: derived branch-specific pure facts before selecting the disjunct.  The empty-string normalization was made explicit:

```coq
rewrite app_Znth2 in H by lia.
replace (0 - Zlength l) with 0 in H by lia.
change (Znth 0 (0 :: nil) 0) with 0 in H.
```

- Result: the final compile replay passed through `string_starts_with_goal_check.v`.

## Final compile and cleanup

- Phenomenon: verify completion requires more than successful `symexec`; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all need a clean replay, then Coq intermediates must be removed.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the base `_CoqProject` load paths and the workspace generated load path:

```bash
-R "$GEN" SimpleC.EE.CAV.verify_20260423_042409_string_starts_with
```

There is no `original/string_starts_with.v`, so that optional step was skipped.  After compile success, removed non-`.v` files under `output/verify_20260423_042409_string_starts_with/coq/` and checked `input/` for non-`.c`/non-`.v` byproducts.
- Result: `logs/compile.log` ends with:

```text
compiled string_starts_with_goal.v
compiled string_starts_with_proof_auto.v
compiled string_starts_with_proof_manual.v
compiled string_starts_with_goal_check.v
compile_end=2026-04-23T04:29:01+08:00
```

Both `logs/coq_non_v_after_cleanup.txt` and `logs/input_non_cv_after_cleanup.txt` are empty.
