# Verification Issues

## Missing loop invariant in the active annotated C

- Phenomenon: the active annotated file initially matched `input/string_all_digits.c` and had no `Inv` before the `while (1)` loop. The loop reads `s[i]`, returns `0` on the first non-digit, increments `i` only after proving the current character is a digit, and returns `1` after reading the terminator. Without a loop invariant, `symexec` would not have a stable way to preserve the full `CharArray::full` resource or relate the processed prefix to `string_all_digits_spec`.
- Triggering C snippet:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] < 48 || s[i] > 57) {
        return 0;
    }
    i++;
}
```

- Fix action: added the invariant in `annotated/verify_20260422_222714_string_all_digits.c`:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      string_all_digits_spec(l1) == 1 &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Why this fixes the issue: `l1` is the accepted digit prefix, `l2` is the unprocessed suffix, `string_all_digits_spec(l1) == 1` is the semantic prefix summary, and the full `CharArray::full` resource is preserved because the function only reads memory. At the `return 0` branches, the current suffix head is a bad character, proving the whole spec returns `0`. At the final `return 1`, the read terminator plus the precondition that all `l[k]` for `k < n` are nonzero proves `i = n`.
- Result: `symexec` succeeded on the annotated file and generated `string_all_digits_goal.v`, `string_all_digits_proof_auto.v`, `string_all_digits_proof_manual.v`, and `string_all_digits_goal_check.v`.

## Symexec generated import shape must match compile load path

- Phenomenon: the first successful `symexec` run generated `proof_manual.v` with `Require Import string_all_digits_goal.` and `goal_check.v` with plain generated imports. This can be inconvenient under the standard workspace compile template, which maps `coq/generated/` to `SimpleC.EE.CAV.verify_20260422_222714_string_all_digits`.
- Trigger command shape:

```text
symexec --goal-file=... --proof-auto-file=... --proof-manual-file=... --goal-check-file=... --input-file=...
```

- Fix action: cleared the generated Coq targets and reran `symexec` with the workspace logical path:

```text
symexec --coq-logic-path=SimpleC.EE.CAV.verify_20260422_222714_string_all_digits \
  --goal-file=... --proof-auto-file=... --proof-manual-file=... \
  --goal-check-file=... --input-file=...
```

- Result: the final `proof_manual.v` and `goal_check.v` import generated files through `From SimpleC.EE.CAV.verify_20260422_222714_string_all_digits Require Import ...`. The final `qcp_run.log` ends with:

```text
Successfully finished symbolic execution
symexec_end: 2026-04-22T22:33:07+08:00
symexec_status: 0
```

## Manual witnesses required list/spec helper lemmas

- Phenomenon: the final generated `coq/generated/string_all_digits_proof_manual.v` contained five manual stubs:

```coq
Lemma proof_of_string_all_digits_entail_wit_1 : string_all_digits_entail_wit_1.
Proof. Admitted.
Lemma proof_of_string_all_digits_entail_wit_2 : string_all_digits_entail_wit_2.
Proof. Admitted.
Lemma proof_of_string_all_digits_return_wit_1 : string_all_digits_return_wit_1.
Proof. Admitted.
Lemma proof_of_string_all_digits_return_wit_2 : string_all_digits_return_wit_2.
Proof. Admitted.
Lemma proof_of_string_all_digits_return_wit_3 : string_all_digits_return_wit_3.
Proof. Admitted.
```

- Localization: all five obligations came from the prefix/suffix invariant `l = app(l1, l2)` in `string_all_digits_goal.v`: invariant initialization, invariant preservation after a good digit, two early bad-character return paths, and the final terminator return path.
- Fix action: replaced the stubs in `coq/generated/string_all_digits_proof_manual.v` with three helper lemmas and concrete witness proofs:

```coq
Lemma string_all_digits_spec_app_digit : ...
Lemma string_all_digits_spec_app_bad_high : ...
Lemma string_all_digits_spec_app_bad_low : ...
```

The witness proofs use `pre_process`, `entailer!`, `prop_apply CharArray.full_length`, `app_Znth2`, `Zlength_app_cons`, and `lia` to connect the C branch facts to the recursive Coq spec.

- Result: `proof_manual.v` contains no `Admitted.` and no added `Axiom`. The final compile log confirms:

```text
compiled: string_all_digits_goal.v
compiled: string_all_digits_proof_auto.v
compiled: string_all_digits_proof_manual.v
compiled: string_all_digits_goal_check.v
```

## Cleanup after successful compile

- Phenomenon: successful `coqc` produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `output/verify_20260422_222714_string_all_digits/coq/generated/`.
- Fix action: removed all non-`.v` files under the workspace `coq/` directory after `goal_check.v` compiled.
- Result: `find output/verify_20260422_222714_string_all_digits/coq -type f ! -name '*.v'` returns no files. `find input -maxdepth 1 -type f ! -name '*.v' ! -name '*.c'` also returns no files.
