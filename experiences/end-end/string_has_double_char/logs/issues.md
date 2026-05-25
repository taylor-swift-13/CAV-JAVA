
## Verify issues for string_has_double_char

### 1. `symexec` silently generated an empty VC module for the original function name

Phenomenon: after adding the loop invariant and exit assertion, `symexec` exited with status 0 but generated `coq/generated/string_has_double_char_goal.v` with only an empty `Module Type VC_Correct` and no function section. The log contained:

```text
Start to symbolic execution on program : annotated/verify_20260423_025651_string_has_double_char.c
Start to print Coq files for the program annotated/verify_20260423_025651_string_has_double_char.c
Successfully finished symbolic execution
```

It did not contain strategy parsing lines or `Symbolic Execution into function ...`, which are present in known-good string examples.

Trigger: the C implementation symbol in the input is `string_has_double_char`. This frontend appears to fail to recognize that function name, likely because it contains the C keyword token `double` as a substring.

Fix action: changed only the active annotated work copy function symbol to `string_has_dup_char` while preserving the exact contract, body, loop invariant, exit assertion, workspace name, and generated file names. The relevant annotated header became:

```c
int string_has_dup_char(char *s)
/*@ With l n
    Require ...
    Ensure ...
*/
```

Result: rerunning `symexec` in the same workspace produced non-empty VCs and the log ended with:

```text
Start to parse strategies file common
Start to parse strategies file char_array
Symbolic Execution into function string_has_dup_char
End of symbolic execution of function string_has_dup_char
Successfully finished symbolic execution
symexec_status=0
```

### 2. Annotated work copy was found truncated and had to be reconstructed

Phenomenon: while applying the annotated-only rename workaround, the active annotated file `annotated/verify_20260423_025651_string_has_double_char.c` was found to be zero bytes. `sed` printed no source and `wc -l` reported `0`.

Impact: the active verify copy no longer contained the input contract, implementation, or annotations, so `symexec` could not be trusted until the file was reconstructed.

Fix action: reconstructed the permitted annotated work copy from `input/string_has_double_char.c`, re-applied the loop invariant and exit assertion, and used the annotated-only function symbol workaround `string_has_dup_char`. The reconstructed loop annotation preserved the processed adjacent-pair property:

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

Result: the reconstructed file was accepted by `symexec`, and the generated VCs correspond to the intended string scan body and contract.

### 3. Manual proof initially depended on fragile generated hypothesis names

Phenomenon: the first `coqc` run failed in `proof_manual.v` with:

```text
Error: No such hypothesis: H
```

After switching to `pre_process`, another generated-hypothesis dependency failed:

```text
Error: The variable H6 was not found in the current environment.
```

Cause: direct `unfold ...; intros` did not decompose the assertion entailment into pure hypotheses, and numbered/generated hypothesis names are unstable across witnesses.

Fix action: started each manual lemma with `pre_process`, then replaced numbered semantic assumptions with shape-based `match goal` selectors for the no-internal-zero fact. Removed two redundant post-`entailer!` `intros` blocks after Coq reported `Error: No such goal.`

Result: `coq/generated/string_has_double_char_proof_manual.v` contains no `Admitted.` and no new `Axiom`; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compile successfully.
