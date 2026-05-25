## Issue 1: unannotated scan loop needed last-index invariant and exit assertion

- Phenomenon: the active annotated copy initially matched `input/string_last_char.c` and had no loop invariant around the unbounded scan:

```c
int i = 0;

while (1) {
    if (s[i + 1] == 0) {
        break;
    }
    i++;
}

return s[i];
```

- Trigger: the postcondition requires `__return == l[n - 1]` while preserving `CharArray::full(s, n + 1, app(l, cons(0, nil)))`. Without an invariant, symbolic execution has no stable fact that `i` stays inside the payload and no loop-exit fact that the break index is `n - 1`.
- Localization: active annotated file `annotated/verify_20260423_120929_string_last_char.c`, around the single `while (1)` loop.
- Fix action: added an `Inv Assert` before the loop preserving `1 <= n`, `n < INT_MAX`, `0 <= i && i < n`, `s == s@pre`, `Zlength(l) == n`, the payload nonzero predicate, and the unchanged `CharArray::full`. Added a post-loop `Assert` immediately before `return s[i]` fixing `i == n - 1` with the same heap and list facts.
- Key fixed annotation:

```c
/*@ Inv Assert
      1 <= n && n < INT_MAX && 0 <= i && i < n &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
while (1) {
    if (s[i + 1] == 0) {
        break;
    }
    i++;
}

/*@ Assert
      1 <= n &&
      n < INT_MAX &&
      i == n - 1 &&
      s == s@pre &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
return s[i];
```

- Result: after clearing stale generated files and rerunning `symexec`, symbolic execution succeeded and generated fresh `string_last_char_goal.v`, `string_last_char_proof_auto.v`, `string_last_char_proof_manual.v`, and `string_last_char_goal_check.v`. `logs/qcp_run.log` ended with:

```text
Successfully finished symbolic execution
symexec_status=0
```

## Issue 2: generated manual proof needed string terminator helper lemmas

- Phenomenon: `coq/generated/string_last_char_proof_manual.v` contained three manual stubs after successful symbolic execution:

```coq
Lemma proof_of_string_last_char_entail_wit_2 : string_last_char_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_last_char_entail_wit_3 : string_last_char_entail_wit_3.
Proof. Admitted.

Lemma proof_of_string_last_char_return_wit_1 : string_last_char_return_wit_1.
Proof. Admitted.
```

- Trigger: the generated VCs needed pure list reasoning about `l ++ 0 :: nil`: a nonzero read at index `i + 1` implies `i + 1 < n`, a zero read at that index implies `i + 1 = n`, and a read at `i = n - 1` stays inside `l`.
- Localization: `output/verify_20260423_120929_string_last_char/coq/generated/string_last_char_goal.v`, definitions `string_last_char_entail_wit_2`, `string_last_char_entail_wit_3`, and `string_last_char_return_wit_1`.
- Fix action: added local helper lemmas to `string_last_char_proof_manual.v`:

```coq
app_zero_at_length
app_zero_nonzero_implies_lt
app_zero_eq_zero_implies_length
app_zero_last_value
```

Then proved each manual witness with `unfold`, `pre_process`, one explicit helper assertion or rewrite, and `entailer!`.

- Result after first proof edit: `goal.v` and `proof_auto.v` compiled, but `proof_manual.v` failed in the return witness with helper inference failure, recorded separately below.

## Issue 3: return witness rewrite needed explicit helper arguments

- Phenomenon: the first strict compile replay stopped at `string_last_char_proof_manual.v` line 106:

```text
compiled string_last_char_goal.v
compiled string_last_char_proof_auto.v
File ".../string_last_char_proof_manual.v", line 106, characters 2-36:
Error: Unable to find an instance for the variable n.
```

- Trigger: the proof used an underspecified rewrite:

```coq
rewrite app_zero_last_value by lia.
```

Coq did not infer the `n` argument of `app_zero_last_value` from the goal reliably, even though the post-`pre_process` context contained `i = n - 1`, `1 <= n`, and `Zlength l = n`.
- Fix action: changed the return witness proof to pin all key helper arguments:

```coq
Lemma proof_of_string_last_char_return_wit_1 : string_last_char_return_wit_1.
Proof.
  unfold string_last_char_return_wit_1.
  pre_process.
  rewrite (app_zero_last_value l n i) by lia.
  entailer!.
Qed.
```

- Result: the second strict replay compiled all four generated files:

```text
compiled string_last_char_goal.v
compiled string_last_char_proof_auto.v
compiled string_last_char_proof_manual.v
compiled string_last_char_goal_check.v
```

## Issue 4: Coq build intermediates required cleanup after successful replay

- Phenomenon: successful `coqc` replay produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `output/verify_20260423_120929_string_last_char/coq/generated/`.
- Trigger: normal Coq compilation of `goal`, `proof_auto`, `proof_manual`, and `goal_check`.
- Fix action: removed all non-`.v` files under the current workspace `coq/` directory with:

```bash
find output/verify_20260423_120929_string_last_char/coq -type f ! -name '*.v' -delete
```

Also checked `input/` for non-`.c`/non-`.v` intermediates; none were present.
- Result: `find output/verify_20260423_120929_string_last_char/coq -type f ! -name '*.v'` returns no files, and `input/` had no cleanup targets.
