# Verify Issues

## Missing loop invariant in initial annotated copy

- Phenomenon: the active annotated file initially matched the input C and had no `Inv` before the `while (1)` scan. Without an invariant, symbolic execution would have no stable relationship between `i`, `count`, `in_word`, the preserved `CharArray::full` resource, and the postcondition `__return == string_count_words_simple_spec(l)`.
- Localization: `annotated/verify_20260423_014132_string_count_words_simple.c`, immediately before:

```c
while (1) {
    if (s[i] == 0) {
        break;
    }
    ...
}
```

- Fix: added a prefix-summary invariant:

```c
count == string_count_words_simple_spec(sublist(0, i, l)) &&
(i == 0 => in_word == 0) &&
(0 < i && in_word == 0 => l[i - 1] == 32) &&
(in_word == 1 => 0 < i && l[i - 1] != 32) &&
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

- Result: after later frontend-shape fixes, `symexec` completed successfully and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Coq bool literals rejected in C annotation frontend

- Phenomenon: the first invariant attempted to use the Coq helper `string_count_words_simple_go(false, ...)` and `string_count_words_simple_go(true, ...)`. `symexec` failed before VC generation:

```text
fatal error: Use of undeclared identifier `false' in .../annotated/verify_20260423_014132_string_count_words_simple.c:40:4
```

- Root cause: the C annotation frontend did not recognize Coq bool literals as annotation identifiers at that program point.
- Fix: removed the direct bool-valued helper from annotations and rewrote the invariant using only the exported `string_count_words_simple_spec` over the processed prefix, plus integer facts describing `in_word`.
- Result: the bool-literal parse error disappeared on the next run.

## `sublist` needed an explicit `Extern Coq` declaration

- Phenomenon: after switching to the prefix invariant, `symexec` failed before VC generation:

```text
fatal error: Use of undeclared identifier `sublist' in .../annotated/verify_20260423_014132_string_count_words_simple.c:37:4
```

- Localization: the invariant line:

```c
count == string_count_words_simple_spec(sublist(0, i, l))
```

- Fix: added the same declaration used by another local string workspace:

```c
/*@ Extern Coq (sublist : {A} -> Z -> Z -> list A -> list A) */
```

- Result: `symexec` progressed past annotation parsing.

## Post-loop assertion omitted live local `in_word`

- Phenomenon: `symexec` reached the loop-exit assertion but failed with:

```text
fatal error: Error: Fail to Remove Memory Permission of in_word:84 in .../annotated/verify_20260423_014132_string_count_words_simple.c:62:4
```

- Root cause: the post-loop assertion mentioned `i` and `count` but not the still-live local variable `in_word`, so the frontend tried to remove its local-store permission at the assertion boundary.
- Fix: added `0 <= in_word && in_word <= 1` to the loop-exit assertion:

```c
/*@ Assert
      i == n &&
      0 <= count && count <= n &&
      0 <= in_word && in_word <= 1 &&
      ...
*/
```

- Result: the next `symexec` run completed:

```text
End of symbolic execution of function string_count_words_simple
Successfully finished symbolic execution
symexec_status=0
```

## Manual proof needed explicit word-count helper lemmas

- Phenomenon: fresh `proof_manual.v` contained five admitted manual witnesses:

```coq
proof_of_string_count_words_simple_entail_wit_1
proof_of_string_count_words_simple_entail_wit_2_1
proof_of_string_count_words_simple_entail_wit_2_2
proof_of_string_count_words_simple_entail_wit_2_3
proof_of_string_count_words_simple_entail_wit_3
```

- Root cause: the remaining goals were pure list/count facts: how `string_count_words_simple_spec (sublist 0 i l)` changes when the next character is a space, a non-space after a space/empty prefix, or a non-space after a non-space.
- Fix: replaced all manual `Admitted.` placeholders with helper lemmas and proofs. Key helpers include:

```coq
sublist_prefix_snoc_Z
string_count_words_simple_spec_app_space
string_count_words_simple_spec_app_space_nonspace
string_count_words_simple_spec_app_nonspace_nonspace
```

- Result: `proof_manual.v` compiled and contains no `Admitted.` and no new `Axiom`.

## Compile and cleanup status

- Compile command working directory: `QualifiedCProgramming/SeparationLogic`.
- Compile result recorded in `logs/coqc_compile.log`:

```text
original passed
goal passed
proof_auto passed
proof_manual passed
goal_check passed
```

- Cleanup: removed non-`.v` Coq build artifacts under `output/verify_20260423_014132_string_count_words_simple/coq/`. No non-`.c`/non-`.v` files were present under repository `input/`.
