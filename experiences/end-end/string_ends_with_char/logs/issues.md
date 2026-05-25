# Verification Issues

## Missing loop invariant for last-character string scan

- Phenomenon: the active annotated file initially matched `input/string_ends_with_char.c` and had no `Inv` before the `while (1)` loop. The implementation scans with `s[i + 1]` until the next character is the terminator, then compares `s[i]` with `c`. Without a loop invariant, symbolic execution would not have a stable bound for `i + 1`, would not preserve the unchanged `CharArray::full` resource, and could not derive that the post-loop `i` is the last valid index.
- Triggering C snippet:

```c
while (1) {
    if (s[i + 1] == 0) {
        break;
    }
    i++;
}

if (s[i] == c) {
    return 1;
}
return 0;
```

- Fix action: added a loop invariant and immediate post-loop assertion to `annotated/verify_20260423_020633_string_ends_with_char.c`:

```c
/*@ Inv Assert
      0 < n && n < INT_MAX && 0 <= i && i < n &&
      s == s@pre &&
      c == c@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
while (1) { ... }

/*@ Assert
      0 < n &&
      n < INT_MAX &&
      i == n - 1 &&
      s == s@pre &&
      c == c@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Why this fixes the issue: after the empty-string guard is skipped, `s[0] != 0` rules out `n == 0`, so `i == 0` satisfies `0 < n` and `0 <= i < n`. On each continuing loop iteration, `s[i + 1] != 0` rules out the appended terminator at index `n`, so the incremented index still satisfies `< n`. On the break path, `s[i + 1] == 0` and the nonzero-prefix precondition force `i + 1 == n`, which gives `i == n - 1` for the final comparison.
- Result: after the final annotation shape, `symexec` succeeded and `logs/qcp_run.log` ended with:

```text
End of symbolic execution of function string_ends_with_char
Successfully finished symbolic execution
```

## Invariant initially dropped `n < INT_MAX`

- Phenomenon: the first successful `symexec` generated manual safety obligations `proof_of_string_ends_with_char_safety_wit_6` and `proof_of_string_ends_with_char_safety_wit_9`. Compiling the first manual proof attempt failed at `safety_wit_6`; `coqtop` showed the remaining pure goal:

```coq
H : 0 < n
H0 : 0 <= i
H1 : i < n
============================
i + 1 <= 2147483647
```

- Cause: the first invariant had `0 < n && 0 <= i && i < n` but did not preserve the precondition fact `n < INT_MAX`, so the integer bound for reading `s[i + 1]` was not provable.
- Fix action: strengthened both the loop invariant and the post-loop assertion with `n < INT_MAX`, cleared stale generated files, and reran `symexec`.
- Result: the regenerated manual proof file no longer had manual safety obligations; only the pure terminator/list obligations remained.

## Manual terminator/list witnesses after symexec

- Phenomenon: the final generated `coq/generated/string_ends_with_char_proof_manual.v` contained five admitted manual obligations:

```coq
proof_of_string_ends_with_char_entail_wit_1
proof_of_string_ends_with_char_entail_wit_2
proof_of_string_ends_with_char_entail_wit_3
proof_of_string_ends_with_char_return_wit_1
proof_of_string_ends_with_char_return_wit_3
```

- Localization: the corresponding VC bodies in `coq/generated/string_ends_with_char_goal.v` prove that the appended `0` terminator is exactly at index `n`, that a nonzero read at `i + 1` implies `i + 1 < n`, that a zero read at `i + 1` implies `i = n - 1`, and that the return branches choose the correct disjunct of the postcondition.
- Fix action: replaced all five stubs with local helper lemmas and concrete proofs in `coq/generated/string_ends_with_char_proof_manual.v`:

```coq
Lemma app_zero_at_length : ...
Lemma app_zero_nonzero_implies_lt : ...
Lemma app_zero_eq_zero_implies_length : ...
Lemma app_zero_last_value : ...
```

The proof bodies use `pre_process`, the helper lemmas, assertion-level `Left`/`Right`, and `entailer!`.
- Result: `string_ends_with_char_proof_manual.v` compiles and `rg -n "Admitted\\.|Axiom" coq/generated/string_ends_with_char_proof_manual.v` finds no proof stubs or new axioms. The only match for `Axioms` is the existing imported library name:

```text
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
```

## Nested postcondition disjunction in `return_wit_3`

- Phenomenon: after proving the nonmatching last-character fact, `return_wit_3` still failed with `Attempt to save an incomplete proof`.
- `coqtop` showed the postcondition parsed as `(case_nonmatch || case_match) || case_empty`. Using only one `Left` selected the outer left side but left the inner disjunction unresolved:

```coq
CharArray.full ... |--
  [|0 < n|] && [|Znth (n - 1) l 0 <> c_pre|] && ...
  || [|0 < n|] && [|Znth (n - 1) l 0 = c_pre|] && ...
```

- Fix action: changed the proof from one branch selection to two assertion-level branch selections:

```coq
Left.
Left.
entailer!.
```

- Result: `proof_manual.v` compiled successfully.

## Non-strict compile wrapper masked the first proof failure

- Phenomenon: an early compile replay used a grouped pipeline without strict stopping inside the group. It reported `compile_status: 0` even though `proof_manual.v` had failed and `goal_check.v` could not import the manual proof.
- Evidence from the old `logs/compile_full.log` before it was overwritten by the final strict replay:

```text
Error:
 (in proof proof_of_string_ends_with_char_safety_wit_6): Attempt to save an incomplete proof
Error: Cannot find a physical path bound to logical path string_ends_with_char_proof_manual ...
compile_status: 0
```

- Fix action: reran compilation with `set -euo pipefail` and direct sequential `coqc` commands, then overwrote `logs/compile_full.log` with the successful strict replay.
- Result: the final compile log records all four generated files compiling in order and ends with `compile_status: 0`.

## Cleanup after successful compile

- Phenomenon: successful `coqc` produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Fix action: removed all non-`.v` files under the current workspace `coq/` directory after `goal_check.v` compiled. Also checked `./input` for non-`.c`/non-`.v` intermediate files.
- Result: both cleanup checks are empty:

```text
find coq -type f ! -name '*.v'
find ./input -maxdepth 1 -type f ! -name '*.c' ! -name '*.v'
```
