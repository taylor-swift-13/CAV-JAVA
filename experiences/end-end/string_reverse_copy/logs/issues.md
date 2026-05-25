## Fingerprint initialized from an empty placeholder

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and `{}` for `keywords`.
- Trigger/location: early verify setup for workspace `output/verify_20260423_041041_string_reverse_copy`; the file contained:

```json
"semantic_description": "",
"keywords": {}
```

- Fix action: read `doc/retrieval/INDEX.md` and filled a concrete description of the reverse string copy loop. The keyword keys and values were restricted to the controlled vocabulary, including `algorithm_family: two_pointers`, `control_flow: for_loop`, `data_shape: ["string", "array", "pointer"]`, `proof_pattern: ["loop_invariant", "heap_reasoning", "range_bound"]`, and `edge_case_behavior: empty_loop_possible`.
- Result: the fingerprint is usable for later retrieval and was updated after success with `verification_status: ["goal_check_passed", "proof_check_passed"]`.

## Missing loop invariant for reversed destination prefix

- Phenomenon: the active annotated C initially copied `input/string_reverse_copy.c` exactly and had no `Inv` before:

```c
for (i = 0; i < n; ++i) {
    dst[i] = src[n - 1 - i];
}
dst[n] = 0;
```

- Trigger/location: `annotated/verify_20260423_041041_string_reverse_copy.c`, immediately before the `for` loop.
- Root cause: the postcondition requires `dst` to become `app(rev(l), cons(0, nil))`, while the loop writes only the first `n` cells and leaves the terminator slot for the later `dst[n] = 0`. Without a loop-head heap expression for the already written reversed prefix and the untouched suffix, symbolic execution cannot preserve the output relation across iterations.
- Fix action: added an invariant that keeps `src`, `dst`, and `n` equal to their pre-state values, preserves source ownership, and describes destination ownership as:

```c
CharArray::full(dst, n@pre + 1,
  app(rev(sublist(n@pre - i, n@pre, l)), sublist(i, n@pre + 1, d)))
```

- Result: after adding the invariant and fixing the `sublist` declaration issue below, `symexec` generated fresh `string_reverse_copy_goal.v`, `string_reverse_copy_proof_auto.v`, `string_reverse_copy_proof_manual.v`, and `string_reverse_copy_goal_check.v`.

## `sublist` was not in scope for the annotated invariant

- Phenomenon: the first `symexec` run with the new invariant failed before VC generation:

```text
fatal error: Use of undeclared identifier `sublist' in annotated/verify_20260423_041041_string_reverse_copy.c:33:4
symexec_status=1
```

- Trigger/location: the invariant used `sublist` in the destination heap expression, but the annotated file had not declared the Coq symbol.
- Fix action: added the same declaration used by the string prefix copy example:

```c
/*@ Extern Coq (sublist : {A} -> Z -> Z -> list A -> list A) */
```

- Result: the rerun completed successfully. The final `logs/qcp_run.log` ended with:

```text
Successfully finished symbolic execution
symexec_end=2026-04-23 04:12:40 +0800
symexec_status=0
```

## Manual proof obligations required reverse-copy list normalization

- Phenomenon: fresh `coq/generated/string_reverse_copy_proof_manual.v` contained three generated placeholders:

```coq
Lemma proof_of_string_reverse_copy_entail_wit_1 : string_reverse_copy_entail_wit_1.
Proof. Admitted.
Lemma proof_of_string_reverse_copy_entail_wit_2 : string_reverse_copy_entail_wit_2.
Proof. Admitted.
Lemma proof_of_string_reverse_copy_return_wit_1 : string_reverse_copy_return_wit_1.
Proof. Admitted.
```

- Trigger/location: `entail_wit_1` is loop initialization, `entail_wit_2` is loop preservation after `dst[i]` is written, and `return_wit_1` is the postcondition after `dst[n] = 0`.
- Fix action: added local helper lemmas in `coq/generated/string_reverse_copy_proof_manual.v`:

```coq
Lemma Zlength_rev_Z : forall (l : list Z), Zlength (rev l) = Zlength l.
Lemma string_reverse_copy_replace_Znth : ...
Lemma string_reverse_copy_final_replace : ...
```

These helpers normalize `replace_Znth` over `rev (sublist ...) ++ sublist ...`, following the existing `examples/reverse_copy` proof pattern but accounting for the extra destination terminator slot and the source read from `l ++ 0 :: nil`.
- Result: the final manual proof file has no `Admitted.` and no top-level `Axiom`; all manual witnesses compile.

## Explicit `sublist_nil` instance needed in final helper

- Phenomenon: the first compile replay after adding manual proofs failed:

```text
File ".../string_reverse_copy_proof_manual.v", line 100, characters 25-28:
Error: Tactic failure: Cannot find witness.
```

- Trigger/location: inside `string_reverse_copy_final_replace`, after:

```coq
rewrite (sublist_split n (n + 1) (n + 1) d) by (pose proof (Zlength_correct d); lia).
rewrite sublist_nil by lia.
```

- Root cause: Coq could not infer the intended instance `sublist (n + 1) (n + 1) d = []` for the polymorphic `sublist_nil` rewrite.
- Fix action: made the instance explicit:

```coq
rewrite (sublist_nil d (n + 1) (n + 1)) by lia.
```

- Result: the fail-fast compile replay succeeded through `string_reverse_copy_goal_check.v`:

```text
compile string_reverse_copy_goal.v
compile string_reverse_copy_proof_auto.v
compile string_reverse_copy_proof_manual.v
compile string_reverse_copy_goal_check.v
compile_status=0
```

## Final cleanup completed

- Phenomenon: Coq compilation produced non-source build artifacts under `coq/generated/`, including `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files.
- Trigger/location: `output/verify_20260423_041041_string_reverse_copy/coq/generated/`.
- Fix action: removed all non-`.v` files under `coq/` and checked for non-`.c`/non-`.v` files under workspace `input/`.
- Result: `find coq input -type f ! -name '*.v' ! -name '*.c' -print` returns no files.
