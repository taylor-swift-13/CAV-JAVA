
## Iteration 1 - add adjacent-pair scan invariant

Context: target function `string_has_double_char` scans the string with `i` initialized to 1. The early branch `if (s[0] == 0) return 0;` covers the empty string case. After that branch, the loop repeatedly reads `s[i]`, exits when it reaches the terminator, returns 1 when `s[i] == s[i - 1]`, and otherwise increments `i`.

Before annotation, the loop has no invariant, so symexec would not have a stable assertion at the `while (1)` control point. The key semantic state at the top of the loop is: `i` is the next index to inspect; all adjacent pairs ending before `i` have already been checked and are unequal; the input string memory remains exactly `CharArray::full(s, n + 1, app(l, cons(0, nil)))`; and the original string pointer and list-length facts are unchanged.

Planned loop annotation before `while (1)`:

```c
/*@ Inv Assert
      1 <= i && i <= n &&
      n < INT_MAX &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (j: Z), (1 <= j && j < i) => l[j] != l[j - 1]) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Why initialization should hold: when execution reaches the loop, `s[0] != 0`. Since the only zero in `app(l, cons(0, nil))` is the terminator at index `n` and every `l[k]` for `0 <= k < n` is nonzero, this implies `n >= 1`; with `i == 1`, the range `1 <= j < i` is empty.

Why preservation should hold: if `s[i] == 0`, the loop exits and does not need preservation. If `s[i] != 0`, then `i < n`; if also `s[i] == s[i - 1]`, the function returns 1 with witness index `i`. Otherwise `s[i] != s[i - 1]`, so after `i++`, the processed range extends from `j < old_i` to `j < old_i + 1` by adding exactly the checked pair at `old_i`.

Why an exit assertion is needed: after `break`, the code only has the loop invariant and the branch fact `s[i] == 0`. The postcondition for return 0 needs the processed-pair property over all `1 <= j < n`, so the proof should explicitly bridge `s[i] == 0` plus the string representation to `i == n`.

Planned loop-exit assertion before `return 0`:

```c
/*@ Assert
      i == n &&
      n < INT_MAX &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (j: Z), (1 <= j && j < n) => l[j] != l[j - 1]) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

This assertion is placed immediately after the loop, before local cleanup at return, matching the existing `string_find_char` pattern for null-terminated scan exits.

## Iteration 2 - frontend did not recognize function name containing `double`

After adding the loop invariant and exit assertion, `symexec` was run with the same command pattern used by the successful `string_find_char` workspace:

```sh
QualifiedCProgramming/linux-binary/symexec \
  --goal-file=coq/generated/string_has_double_char_goal.v \
  --proof-auto-file=coq/generated/string_has_double_char_proof_auto.v \
  --proof-manual-file=coq/generated/string_has_double_char_proof_manual.v \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260423_025651_string_has_double_char \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --input-file=annotated/verify_20260423_025651_string_has_double_char.c \
  --no-exec-info
```

The command exited with status 0, but the generated `string_has_double_char_goal.v` contained only an empty `Module Type VC_Correct` and no `(*----- Function ... -----*)` section. Running without `--no-exec-info` also printed only:

```text
Start to symbolic execution on program : .../verify_20260423_025651_string_has_double_char.c
Start to print Coq files for the program .../verify_20260423_025651_string_has_double_char.c
Successfully finished symbolic execution
```

It did not print `Start to parse strategies file common` or `Symbolic Execution into function ...`, unlike the known-good `string_find_char` run. The annotated function name contains the C keyword token `double` as a substring: `string_has_double_char`. This appears to trigger a frontend symbol-recognition bug where the file is accepted but the function is skipped.

Planned workaround in the active annotated copy only: rename the C implementation symbol from `string_has_double_char` to `string_has_dup_char`. This does not change the function body, specification, memory contract, or target semantic proof obligations; it only avoids the frontend identifier issue so `symexec` can generate VCs. The workspace and generated file names remain `string_has_double_char_*` so the verification artifacts still belong to the requested task.
