# Verification Issues

## No annotation changes were needed

- Phenomenon: the active annotated file `annotated/verify_20260423_043145_string_starts_with_char.c` matched the input implementation and contained no `Inv`, `Assert`, or `which implies` additions.
- Trigger: initial verify review of `string_starts_with_char`, whose control flow is straight-line branching:

```c
if (s[0] == 0) {
    return 0;
}
if (s[0] == c) {
    return 1;
}
return 0;
```

- Reason: the contract already supplies `Zlength(l) == n`, the no-internal-zero fact for indices `0 <= k < n`, and `CharArray::full(s, n + 1, app(l, cons(0, nil)))`. Those facts are enough for all branch return witnesses; there is no loop summary to add.
- Result: no `logs/annotation_reasoning.md` was created, and `symexec` ran against the unchanged active annotated C file.

## Fresh symexec succeeded and generated three manual return witnesses

- Phenomenon: before `symexec`, the workspace had no generated Coq VC files under `coq/generated/`.
- Triggering command shape:

```text
QualifiedCProgramming/linux-binary/symexec
  --goal-file=.../coq/generated/string_starts_with_char_goal.v
  --proof-auto-file=.../coq/generated/string_starts_with_char_proof_auto.v
  --proof-manual-file=.../coq/generated/string_starts_with_char_proof_manual.v
  --goal-check-file=.../coq/generated/string_starts_with_char_goal_check.v
  --input-file=annotated/verify_20260423_043145_string_starts_with_char.c
  --coq-logic-path=SimpleC.EE.CAV.verify_20260423_043145_string_starts_with_char
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE
  --no-exec-info
```

- Result: `logs/qcp_run.log` ended with:

```text
End of symbolic execution of function string_starts_with_char
Successfully finished symbolic execution
symexec_status=0
```

The generated manual proof file initially contained these placeholders:

```coq
Lemma proof_of_string_starts_with_char_return_wit_1 : string_starts_with_char_return_wit_1.
Proof. Admitted.

Lemma proof_of_string_starts_with_char_return_wit_2 : string_starts_with_char_return_wit_2.
Proof. Admitted.

Lemma proof_of_string_starts_with_char_return_wit_3 : string_starts_with_char_return_wit_3.
Proof. Admitted.
```

## Assertion disjunction branch selection was left-associated

- Phenomenon: the first manual proof attempt for `return_wit_1` compiled `goal.v` and `proof_auto.v`, then failed in `proof_manual.v`:

```text
File ".../string_starts_with_char_proof_manual.v", line 34, characters 9-14:
Error: Found no subterm matching "?e || ?e0" in the current goal.
```

- Triggering proof snippet:

```coq
Right. Right.
entailer!.
```

- Cause: the generated three-way postcondition is parsed as `(first || second) || third`, so after the first `Right` the proof is already at the third disjunct. A second `Right` has no remaining assertion-level disjunction to select.
- Fix action: changed the branch selectors to match the left-associated shape:

```coq
(* third disjunct *)
Right.

(* second disjunct *)
Left. Right.

(* first disjunct *)
Left. Left.
```

- Result: the disjunction selector error was removed; the next compile progressed to the arithmetic/list contradiction inside `return_wit_2`.

## Nonzero terminator contradiction needed explicit length rewrite

- Phenomenon: after fixing branch selectors, `proof_manual.v` failed in `return_wit_2`:

```text
File ".../string_starts_with_char_proof_manual.v", line 48, characters 6-19:
Error: No such contradiction
```

- Triggering proof branch: the script tried to prove `0 < n` from the hypothesis that the first read from `l ++ [0]` was nonzero. In the `n = 0` case, it originally rewrote the equality-to-`c_pre` hypothesis instead of the nonzero-read hypothesis, which only produced `0 = c_pre` and did not contradict anything.
- Fix action: rewrote the nonzero-read hypothesis with `app_Znth2`, then explicitly rewrote the local length equality before simplification:

```coq
subst n.
rewrite app_Znth2 in H0 by lia.
rewrite Hz in H0.
simpl in H0.
contradiction.
```

The same explicit `rewrite Hz in H0` was applied to `return_wit_3`, which has the same nonzero-read contradiction.

- Result: `string_starts_with_char_proof_manual.v` compiled successfully, and the final full replay compiled:

```text
compiled string_starts_with_char_goal.v
compiled string_starts_with_char_proof_auto.v
compiled string_starts_with_char_proof_manual.v
compiled string_starts_with_char_goal_check.v
```

## Final cleanup

- Phenomenon: successful `coqc` replay created `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` build artifacts under `coq/generated/`.
- Fix action: deleted every file under `coq/` whose name does not end in `.v`.
- Result: `find coq -type f ! -name '*.v'` produced no output, and `./input` had no non-`.c`/non-`.v` byproducts to remove.
