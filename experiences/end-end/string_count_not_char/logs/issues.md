# Verification Issues

## Fingerprint metadata was initially empty

- Phenomenon: `logs/workspace_fingerprint.json` had an empty `semantic_description` and `{}` for `keywords`, even though the verify workflow requires these fields to be filled early and requires all keyword keys/values to come from `doc/retrieval/INDEX.md`.
- Trigger: initial workspace state before annotation or symbolic execution.
- Localization: `output/verify_20260423_005835_string_count_not_char/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled the semantic description for a read-only null-terminated string scan that counts characters not equal to `c`. Keywords were restricted to controlled values including `counting`, `while_loop`, `string`, `array`, `pointer`, `preserve_input`, `loop_invariant`, `case_split`, `termination_by_bound`, `heap_reasoning`, `nonnegative_input`, `int_range`, `monotone_accumulator`, and `empty_loop_possible`.
- Result: the fingerprint now has non-empty semantic metadata. After successful verification, `verification_status` was updated to include `manual_witness_needed`, `goal_check_passed`, `proof_check_passed`, `auto_proof_contains_admitted`, and `generated_goal_contains_axioms`.

## Missing loop invariant for prefix count

- Phenomenon: the active annotated C initially matched the input and had no `Inv` before the `while (1)` loop. Without an invariant, symbolic execution would have no stable relation between `i`, `count`, the processed prefix of `l`, and `string_count_not_char_spec`.
- Triggering C snippet:

```c
int i = 0;
int count = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] != c) {
        count++;
    }
    i++;
}
```

- Localization: `annotated/verify_20260423_005835_string_count_not_char.c`, immediately before the only loop.
- Fix action: added a prefix/suffix invariant that splits `l` into `l1` and `l2`, records `Zlength(l1) == i`, records `count == string_count_not_char_spec(l1, c)`, keeps `0 <= count && count <= i` for `count++` safety, preserves `s == s@pre` and `c == c@pre`, carries `Zlength(l) == n` and the no-internal-zero fact, and keeps the unchanged heap resource:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= count && count <= i &&
      s == s@pre &&
      c == c@pre &&
      Zlength(l) == n &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      count == string_count_not_char_spec(l1, c) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Why this fixes the issue: at loop entry, `l1` is the processed prefix and `count` is exactly the number of processed characters not equal to `c`. On a continuing iteration, the current suffix head is appended to `l1`; the spec either increases by `1` when the character is not `c`, or stays unchanged when the character equals `c`. On the break path, the zero read and the no-internal-zero contract force `i == n`, so `l2` is empty and the prefix count is the full-list count.
- Result: `symexec` accepted the annotated file and generated fresh `string_count_not_char_goal.v`, `string_count_not_char_proof_auto.v`, `string_count_not_char_proof_manual.v`, and `string_count_not_char_goal_check.v`. `logs/qcp_run.log` ends with:

```text
End of symbolic execution of function string_count_not_char
Successfully finished symbolic execution
symexec_status=0
```

## Manual witnesses required list/spec helper lemmas

- Phenomenon: after successful symbolic execution, `coq/generated/string_count_not_char_proof_manual.v` contained four generated `Admitted.` placeholders:

```coq
Lemma proof_of_string_count_not_char_entail_wit_1 : string_count_not_char_entail_wit_1.
Proof. Admitted.
Lemma proof_of_string_count_not_char_entail_wit_2_1 : string_count_not_char_entail_wit_2_1.
Proof. Admitted.
Lemma proof_of_string_count_not_char_entail_wit_2_2 : string_count_not_char_entail_wit_2_2.
Proof. Admitted.
Lemma proof_of_string_count_not_char_return_wit_1 : string_count_not_char_return_wit_1.
Proof. Admitted.
```

- Localization: `output/verify_20260423_005835_string_count_not_char/coq/generated/string_count_not_char_proof_manual.v`.
- Fix action: added local helper lemmas in `proof_manual.v` for `string_count_not_char_spec` over append and over one appended character in the equal/not-equal cases:

```coq
Lemma string_count_not_char_spec_app : ...
Lemma string_count_not_char_spec_app_single_neq : ...
Lemma string_count_not_char_spec_app_single_eq : ...
```

The preservation witnesses destruct the unprocessed suffix, choose the next invariant prefix `l1_2 ++ x :: nil`, and use the branch fact `x <> c_pre` or `x = c_pre` with the corresponding helper lemma. The return witness first proves `i = n` from the terminating-zero read and the no-internal-zero precondition, then proves the suffix is empty from the length equations.
- Result: `proof_manual.v` compiles and `rg -n "Admitted\\.|^Axiom\\b" coq/generated/string_count_not_char_proof_manual.v` returns no matches.

## Brittle proof script points during compilation

- Phenomenon: the first compile of `proof_manual.v` failed at line 79 with:

```text
Error: No such contradiction
```

The branch had simplified a terminator read to a contradiction, but `contradiction` did not close it reliably.
- Fix action: replaced the implicit tactic with an explicit contradiction:

```coq
exfalso.
apply H0.
reflexivity.
```

- Result: compilation moved past that branch.

- Phenomenon: the next compile failed because the index in the simplified terminator read was not syntactically the expression the proof tried to rewrite:

```text
H0 : Znth (Zlength l1_2 - Zlength l) (0 :: nil) 0 <> 0
Unable to unify "0" with "Znth (Zlength l1_2 - Zlength l) (0 :: nil) 0".
```

- Fix action: changed the rewrite from `replace (n - Zlength l) with 0 in H0 by lia` to:

```coq
replace (Zlength l1_2 - Zlength l) with 0 in H0 by lia.
```

- Result: the preservation witnesses compiled.

- Phenomenon: the return witness initially copied numbered hypotheses from a close string example and failed because this task's extra invariant facts shifted the generated names:

```text
Error: Found no subterm matching "0" in the current goal.
Error: No matching clauses for match.
```

- Fix action: replaced numbered references with `match goal` patterns for the concrete shape and count hypotheses, and removed an unnecessary `symmetry` because the goal direction already matched `count = string_count_not_char_spec l1 c_pre`.
- Result: the full compile replay passed:

```text
compiled: original/string_count_not_char.v
compiled: string_count_not_char_goal.v
compiled: string_count_not_char_proof_auto.v
compiled: string_count_not_char_proof_manual.v
compiled: string_count_not_char_goal_check.v
compile_status=0
```

## Cleanup after successful compile

- Phenomenon: `coqc` produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `output/verify_20260423_005835_string_count_not_char/coq/generated/`.
- Trigger: normal successful compilation of `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`.
- Fix action: after `goal_check.v` compiled successfully, deleted all non-`.v` files under `output/verify_20260423_005835_string_count_not_char/coq`.
- Result: `find output/verify_20260423_005835_string_count_not_char/coq -type f ! -name '*.v'` returns no files. `find input -maxdepth 1 -type f ! -name '*.c' ! -name '*.v'` also returns no files.
