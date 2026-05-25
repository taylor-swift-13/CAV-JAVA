# Verify Issues: reverse_digits

## Summary

- Final status: success.
- Active annotated C: `annotated/verify_20260422_214114_reverse_digits.c`.
- Workspace: `output/verify_20260422_214114_reverse_digits`.
- `symexec` succeeded on the latest annotated file.
- `reverse_digits_goal.v`, `reverse_digits_proof_auto.v`, `reverse_digits_proof_manual.v`, and `reverse_digits_goal_check.v` all compiled with the current workspace load paths.
- `reverse_digits_proof_manual.v` contains no `Admitted.` and no new `Axiom`.

## Fingerprint placeholder had to be filled

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and `{}` keywords.
- Trigger: the workspace was created before semantic backfill.
- Localization: `output/verify_20260422_214114_reverse_digits/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a nonempty semantic description and used only controlled vocabulary values: `accumulation`, `while_loop`, `scalar_only`, `loop_invariant`, `pure_arithmetic`, `termination_by_bound`, `nonnegative_input`, `overflow_guard`, `monotone_accumulator`, and `empty_loop_possible`. After successful `goal_check`, added `verification_status` values `goal_check_passed` and `proof_check_passed`.
- Result: the fingerprint now describes the scalar digit-reversal accumulator loop and records successful verification status.

## Missing loop invariant for accumulator digit reversal

- Phenomenon: the active annotated C initially matched the input implementation and had no invariant for `while (n > 0)`. Without an invariant, the verifier had no loop-head relation between shrinking `n`, accumulator `ans`, and the original value `n@pre` required by the postcondition.
- Trigger: the postcondition is `__return == reverse_digits_z(n@pre)`, but the loop mutates both `n` and `ans`.
- Localization: `annotated/verify_20260422_214114_reverse_digits.c`, immediately before the loop.
- Fix action: added a parser-facing helper and invariant:

```c
/*@ Extern Coq (reverse_digits_acc_z : Z -> Z -> Z) */
/*@ Import Coq Require Import reverse_digits_verify_aux */
...
/*@ Inv
      0 <= n &&
      n <= INT_MAX &&
      0 <= ans &&
      ans <= reverse_digits_z(n@pre) &&
      reverse_digits_z(n@pre) <= INT_MAX &&
      reverse_digits_acc_z(n, ans) == reverse_digits_z(n@pre)
*/
while (n > 0) {
```

- Result: the invariant preserves the semantic accumulator relation needed for loop preservation and final return.

## Parser-friendly helper was needed for fuelled Coq definition

- Phenomenon: the natural invariant relation is `reverse_digits_acc_fuel n ans (Z.to_nat n)`, but direct `Z.to_nat` terms are not stable in C annotations.
- Trigger: `input/reverse_digits.v` defines `reverse_digits_z` using a fuelled helper whose fuel is a `nat`, while C annotations need first-order parser-facing symbols.
- Localization: `output/verify_20260422_214114_reverse_digits/coq/deps/reverse_digits_verify_aux.v`.
- Fix action: added:

```coq
Definition reverse_digits_acc_z (n acc : Z) : Z :=
  reverse_digits_acc_fuel n acc (Z.to_nat n).
```

- Result: `symexec` accepted the annotated file and generated VCs containing `reverse_digits_acc_z`.

## Local `int` upper bound needed an explicit `by local` bridge

- Phenomenon: first proof attempt after the initial invariant generated an unprovable initialization side condition:

```coq
H  : 0 <= n_pre
H0 : 0 <= reverse_digits_z n_pre
H1 : reverse_digits_z n_pre <= 2147483647
============================
n_pre <= 2147483647
```

- Trigger: the invariant included `n <= INT_MAX`, but the invariant-initialization VC did not retain the C local-store representability fact for parameter `n`.
- Localization: `proof_of_reverse_digits_entail_wit_1` in the first generated `reverse_digits_proof_manual.v`; annotation point after `ans = 0`.
- Fix action: added the documented local bridge before the loop:

```c
/*@ n <= INT_MAX by local */
```

- Result: after rerunning `symexec`, the local bridge generated its own `entail_wit_1`, carried `n_pre <= INT_MAX` into the loop invariant, and the initialization witness no longer required an impossible proof from the formal precondition alone.

## Manual proof needed accumulator and division helper lemmas

- Phenomenon: fresh `proof_manual.v` after the final `symexec` contained five `Admitted.` stubs: `safety_wit_3`, `safety_wit_5`, `entail_wit_2`, `entail_wit_3`, and `entail_wit_4`.
- Trigger: automatic proof could not unfold the fuelled accumulator relation, connect one C loop step to the Coq helper, or prove accumulator overflow bounds from the final result guard.
- Localization: `output/verify_20260422_214114_reverse_digits/coq/generated/reverse_digits_proof_manual.v`.
- Fix action: added local lemmas for quotient/division bounds, fuel stability, one positive accumulator step, zero exit, initialization, and accumulator monotonicity. The key step lemma is:

```coq
Lemma reverse_digits_acc_z_step :
  forall n acc,
    0 < n ->
    reverse_digits_acc_z n acc =
    reverse_digits_acc_z (n ÷ 10) (acc * 10 + n % 10).
```

- Result: all five manual witnesses compile with concrete proofs, and `rg "Admitted\\.|Axiom" reverse_digits_proof_manual.v` only matches the imported module name `Axioms`, not an admitted proof or new axiom declaration.

## Coq `Z.div` and C quotient notation had to be bridged

- Phenomenon: an intermediate proof failed with:

```text
Found no subterm matching
"reverse_digits_acc_fuel (n ÷ 10) (acc * 10 + n % 10) (fuel + extra)"
in the current goal.
```

- Trigger: `reverse_digits_acc_fuel` from `input/reverse_digits.v` recurses with `Z.div`, displayed as `n / 10`, while generated C VCs use quotient notation `n ÷ 10`.
- Localization: helper lemmas `reverse_digits_acc_fuel_stable` and `reverse_digits_acc_z_step` in `reverse_digits_proof_manual.v`.
- Fix action: used `/` in the fuel-stability and accumulator-growth lemmas, and used `Z.quot_div_nonneg` to replace `n / 10` with `n ÷ 10` under `0 <= n` and `0 < 10`.
- Result: the helper lemmas compiled and the loop-preservation witness could rewrite from the invariant state to the post-body state.

## Cleanup

- Phenomenon: successful `coqc` compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/deps/` and `coq/generated/`.
- Trigger: normal Coq compilation output.
- Localization: `output/verify_20260422_214114_reverse_digits/coq/`.
- Fix action: deleted all non-`.v` files under the workspace `coq/` directory and confirmed `input/` contained no non-`.c`/non-`.v` intermediates.
- Result: `find output/verify_20260422_214114_reverse_digits/coq -type f ! -name '*.v'` prints no files.
