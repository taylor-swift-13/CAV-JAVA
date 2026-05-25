# Verification Issues

## Missing loop invariant for string scan

- Phenomenon: the active annotated C initially matched `input/string_contains_char.c` and had no `Inv` before the `while (1)` loop. The implementation reads `s[i]`, breaks on `s[i] == 0`, returns `1` on `s[i] == c`, and otherwise increments `i`. Without an invariant, symbolic execution has no stable fact connecting `i` to the already scanned prefix or to `string_contains_char_spec(l, c)`.
- Triggering C snippet:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == c) {
        return 1;
    }
    i++;
}

return 0;
```

- Fix action: added a prefix/suffix loop invariant in `annotated/verify_20260422_234921_string_contains_char.c`:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      s == s@pre &&
      c == c@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      string_contains_char_spec(l1, c) == 0 &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Why this fixes the issue: `l1` is the processed prefix, `l2` is the unprocessed suffix, and `string_contains_char_spec(l1, c) == 0` records that no earlier scanned character matched `c`. The invariant also preserves `s == s@pre`, `c == c@pre`, the nonzero-prefix contract, and the full string resource. On the `s[i] == c` branch, the suffix head is a matching character and the full spec becomes `1`; on the `s[i] == 0` branch, the nonzero-prefix contract forces `i == n`, so the prefix summary covers all of `l`.
- Result: `symexec` succeeded and generated fresh `string_contains_char_goal.v`, `string_contains_char_proof_auto.v`, `string_contains_char_proof_manual.v`, and `string_contains_char_goal_check.v`. The log ended with:

```text
End of symbolic execution of function string_contains_char
Successfully finished symbolic execution
symexec_status=0
```

## Manual witnesses required list/spec helper lemmas

- Phenomenon: after successful symbolic execution, `coq/generated/string_contains_char_proof_manual.v` contained four admitted manual obligations:

```coq
Lemma proof_of_string_contains_char_entail_wit_1 : string_contains_char_entail_wit_1.
Proof. Admitted.
Lemma proof_of_string_contains_char_entail_wit_2 : string_contains_char_entail_wit_2.
Proof. Admitted.
Lemma proof_of_string_contains_char_return_wit_1 : string_contains_char_return_wit_1.
Proof. Admitted.
Lemma proof_of_string_contains_char_return_wit_2 : string_contains_char_return_wit_2.
Proof. Admitted.
```

- Localization: the generated goal file defines the four manual obligations at `coq/generated/string_contains_char_goal.v` lines 146, 166, 194, and 213. The core hard cases were extending the prefix after a nonmatching character, proving the full spec is `1` on the matching branch, and proving `i == n` on the terminating-zero branch.
- Fix action: replaced the stubs in `coq/generated/string_contains_char_proof_manual.v` with two helper lemmas and concrete witness proofs:

```coq
Lemma string_contains_char_spec_app_single : ...
Lemma string_contains_char_spec_app_hit : ...
```

The witness proofs use `pre_process`, `entailer!`, `prop_apply CharArray.full_length`, `app_Znth1`, `app_Znth2`, `Zlength_app_cons`, and `lia` to connect the C branch facts to the recursive Coq spec.

- Result: `proof_manual.v` contains no `Admitted.` and no added `Axiom`. The full compile replay succeeded:

```text
compiled: original/string_contains_char.v
compiled: string_contains_char_goal.v
compiled: string_contains_char_proof_auto.v
compiled: string_contains_char_proof_manual.v
compiled: string_contains_char_goal_check.v
compile_status=0
```

## Cleanup after successful compile

- Phenomenon: successful `coqc` produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `output/verify_20260422_234921_string_contains_char/coq/generated/`.
- Fix action: removed all non-`.v` files under the workspace `coq/` directory after `goal_check.v` compiled. Also checked `input/` for non-`.c`/non-`.v` intermediates.
- Result: `find output/verify_20260422_234921_string_contains_char/coq -type f ! -name '*.v'` returns no files, and `find input -maxdepth 1 -type f ! -name '*.v' ! -name '*.c'` returns no files.
