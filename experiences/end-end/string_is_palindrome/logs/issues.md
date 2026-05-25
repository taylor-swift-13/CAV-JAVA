# Issues

## Empty workspace fingerprint metadata

- Phenomenon: `logs/workspace_fingerprint.json` initially contained an empty `semantic_description` and `{}` for `keywords`, which violates the verify workflow requirement that the fingerprint be useful for later retrieval.
- Trigger: early workspace inspection before annotation or symbolic execution.
- Location: `output/verify_20260423_031617_string_is_palindrome/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a nonempty description of the read-only two-pointer palindrome check. The `keywords` object uses only controlled keys and values from the index, including `two_pointers`, `while_loop`, `string`, `loop_invariant`, `range_bound`, and final `verification_status` values `goal_check_passed` and `proof_check_passed`.
- Result: the fingerprint now describes the program, input/output relation, control flow, edge case `n <= 1`, and memory preservation.

## Missing loop invariant for palindrome two-pointer scan

- Phenomenon: the active annotated C initially copied the input implementation without any `Inv` before the `while (left < right)` loop:

```c
int left = 0;
int right = n - 1;

while (left < right) {
    if (s[left] != s[right]) {
        return 0;
    }
    left++;
    right--;
}
```

- Trigger: the loop both reads symmetric array positions and accumulates semantic knowledge across iterations. The return `0` path needs an existential mismatch witness, while the final return `1` path needs a universal symmetric equality over the whole list.
- Location: `annotated/verify_20260423_031617_string_is_palindrome.c`, immediately before the `while (left < right)` loop.
- Fix action: added a complete loop invariant at the true loop-head control point:

```c
/*@ Inv Assert
      0 <= left && left <= n &&
      right == n - 1 - left &&
      -1 <= right && right < n &&
      n == n@pre &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < left) => l[k] == l[n - 1 - k]) &&
      CharArray::full(s, n, l)
*/
```

- Why this fixes the issue: the bounds and `right == n - 1 - left` make the guarded reads safe and identify the mismatch index on early return. The quantified prefix fact records every checked symmetric pair; on loop exit, `left >= right` plus the pointer equation makes every remaining non-middle index mirror into that checked prefix. The heap predicate stays as `CharArray::full(s, n, l)` because the function never writes to `s`.
- Result: rerunning `symexec` on the updated annotated file succeeded. `logs/qcp_run.log` ended with:

```text
End of symbolic execution of function string_is_palindrome
Successfully finished symbolic execution
symexec_status=0
```

## Coq compile intermediates after successful proof check

- Phenomenon: successful `coqc` compilation produced non-source files under `output/verify_20260423_031617_string_is_palindrome/coq/generated/`, including `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files.
- Trigger: normal Coq compilation of `string_is_palindrome_goal.v`, `string_is_palindrome_proof_auto.v`, `string_is_palindrome_proof_manual.v`, and `string_is_palindrome_goal_check.v`.
- Location: `output/verify_20260423_031617_string_is_palindrome/coq/generated/`.
- Fix action: after `goal_check.v` compiled successfully, removed all files under the workspace `coq/` directory whose names do not end in `.v`; also checked `input/` for non-`.c`/non-`.v` intermediates.
- Result: `find output/verify_20260423_031617_string_is_palindrome/coq -type f ! -name '*.v'` returns no files, and `find input -maxdepth 1 -type f ! -name '*.c' ! -name '*.v'` returns no files.
