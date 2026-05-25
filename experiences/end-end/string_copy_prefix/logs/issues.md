# Issues

## Missing `sublist` declaration for char-array contract

- Phenomenon: the first `symexec` run failed before VC generation:

```text
fatal error: Use of undeclared identifier `sublist' in annotated/verify_20260423_000831_string_copy_prefix.c:19:1
```

- Trigger: `input/string_copy_prefix.c` and the active annotated copy use `sublist` in the postcondition:

```c
CharArray::full(dst, k@pre + 1,
  app(sublist(0, k@pre, l), cons(0, nil)))
```

but `char_array_def.h` declares `CharArray` predicates, `Znth`, `replace_Znth`, and `repeat_Z`, not `sublist`. The comparable `int_array_def.h` does declare:

```c
/*@ Extern Coq (sublist : {A} -> Z -> Z -> list A -> list A) */
```

- Location: active annotated file `annotated/verify_20260423_000831_string_copy_prefix.c`, near the includes and function contract.
- Fix action: added the same `Extern Coq` declaration for `sublist` in the active annotated copy only:

```c
/*@ Extern Coq (sublist : {A} -> Z -> Z -> list A -> list A) */
```

- Result: the undeclared identifier error was removed, allowing the frontend to continue parsing the contract.

## `@pre` inside `sublist` argument rejected by frontend

- Phenomenon: after declaring `sublist`, `symexec` still failed before checking the loop invariant:

```text
fatal error: Expected C expression in annotated/verify_20260423_000831_string_copy_prefix.c:21:1
Now parsing : n with type :2
```

- Trigger: the active annotated postcondition had `@pre` expressions inside and near the polymorphic `sublist` call:

```c
CharArray::full(src, n@pre + 1, app(l, cons(0, nil))) *
CharArray::full(dst, k@pre + 1,
  app(sublist(0, k@pre, l), cons(0, nil)))
```

- Location: active annotated file `annotated/verify_20260423_000831_string_copy_prefix.c`, function postcondition.
- Fix action: normalized only the active annotated copy to use unchanged parameters directly:

```c
CharArray::full(src, n + 1, app(l, cons(0, nil))) *
CharArray::full(dst, k + 1,
  app(sublist(0, k, l), cons(0, nil)))
```

The C function never assigns to `k`, `src`, or `dst`; the invariant also records `src == src@pre`, `dst == dst@pre`, and `k == k@pre`. This was a parser-stability normalization in the Verify working copy. The official `input/string_copy_prefix.c` was not modified.

- Result: the next `symexec` run completed successfully and generated fresh `string_copy_prefix_goal.v`, `string_copy_prefix_proof_auto.v`, `string_copy_prefix_proof_manual.v`, and `string_copy_prefix_goal_check.v` under the current workspace.

## Manual proof hypothesis-number drift

- Phenomenon: the initial manual proof, adapted from `string_copy`, failed several times because generated hypothesis numbers differed in this bounded-prefix VC:

```text
Error: [Focus] Wrong bullet -: No more goals.
Error: Found no subterm matching "Zlength nil" in H4.
Error: No matching clauses for match.
Unable to unify "Zlength l = n" with "Znth k l1 0 = Znth (k + 0) l 0".
Unable to unify "k + 0" with "k".
```

- Trigger: the `string_copy` proof pattern was semantically close, but this VC uses `k_pre` as the final boundary rather than deriving `i = n` from a source terminator. Also, `pre_process` renamed the loop index in the return witness to `Zlength l1`, and the relevant suffix length and prefix equality facts were not at the same hypothesis numbers as in the source proof.
- Location: `output/verify_20260423_000831_string_copy_prefix/coq/generated/string_copy_prefix_proof_manual.v`, lemmas `proof_of_string_copy_prefix_entail_wit_1`, `proof_of_string_copy_prefix_entail_wit_2`, and `proof_of_string_copy_prefix_return_wit_1`.
- Fix action:
  - Removed the stale bullet after `entailer!` in `entail_wit_1`.
  - In `entail_wit_2`, named the cons-suffix length fact before rewriting it, chose `l1 = l1_2 ++ [Znth i_2 l 0]` and `d1 = l0`, and used the actual prefix hypothesis `H10`.
  - In `return_wit_1`, proved `l1 = sublist 0 k_pre l` using `list_eq_ext`, `Zlength_sublist`, `Znth_sublist`, and the invariant prefix hypothesis; then destructed the one-cell suffix and normalized `replace_Znth`.

- Result: the final compile replay succeeded through `string_copy_prefix_goal_check.v`; `string_copy_prefix_proof_manual.v` contains no `Admitted.` and no local `Axiom`.

## Cleanup after successful compile

- Phenomenon: successful `coqc` produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `output/verify_20260423_000831_string_copy_prefix/coq/generated/`.
- Fix action: removed all non-`.v` files under the workspace `coq/` directory after `goal_check.v` compiled. Also checked `input/` for non-`.c`/non-`.v` intermediates.
- Result: `find output/verify_20260423_000831_string_copy_prefix/coq -type f ! -name '*.v'` returns no files, and `find input -maxdepth 1 -type f ! -name '*.c' ! -name '*.v'` returns no files.
