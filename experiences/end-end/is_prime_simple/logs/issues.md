# Verification Issues

## Fingerprint completion

- Phenomenon: the workspace was initialized with an empty `semantic_description` and empty `keywords`.
- Trigger: the verify task requires filling `logs/workspace_fingerprint.json` early, after reading `doc/retrieval/INDEX.md`, and the keywords must use only the controlled vocabulary from that index.
- Localization: `output/verify_20260422_180530_is_prime_simple/logs/workspace_fingerprint.json`.
- Fix: filled `semantic_description` with the scalar primality-search behavior: return 0 for `n < 2`, scan candidate divisors `d = 2..n-1`, return 0 on `n % d == 0`, otherwise return 1; used controlled keywords including `algorithm_family: search`, `control_flow: [if, for_loop]`, `data_shape: scalar_only`, and proof-pattern entries for loop invariants and pure arithmetic.
- Result: the fingerprint is non-empty, uses only controlled key/value terms, and after final compile records `verification_status: [goal_check_passed, proof_check_passed]`.

## Missing divisor-scan invariant

- Phenomenon: the active annotated C initially had no invariant for `for (d = 2; d < n; ++d)`, so the verifier had no durable fact connecting the final `return 1` to the Coq primality specification.
- Trigger: the final positive result requires proving `forall d, 2 <= d < n -> n % d <> 0`; without a loop invariant, that processed-divisor fact is not preserved across iterations.
- Localization: `annotated/verify_20260422_180530_is_prime_simple.c`, immediately before the `for` loop and immediately after loop exit.
- Fix: added the loop invariant:

```c
/*@ Inv
      0 <= n && n <= INT_MAX &&
      n == n@pre &&
      2 <= d && d <= n &&
      (forall (k: Z), (2 <= k && k < d) => n % k != 0) &&
      emp
*/
```

and the loop-exit assertion:

```c
/*@ Assert
      n == n@pre &&
      2 <= n &&
      d == n &&
      (forall (k: Z), (2 <= k && k < n) => n % k != 0) &&
      emp
*/
```

- Result: after the final clean `symexec`, the generated `return_wit_3` had exactly the lower bound and universal nonzero-remainder facts needed to prove `is_prime_simple_spec n 1`.

## Local integer upper-bound bridge

- Phenomenon: the first successful `symexec` generated `is_prime_simple_entail_wit_1` with a pure obligation to prove `n_pre <= INT_MAX` from only `n_pre >= 2` and `0 <= n_pre`.
- Trigger: the invariant needs `n <= INT_MAX` to prove the `d + 1` safety bound, but the function-level `Require` only states `0 <= n`; the upper bound comes from the C `int` local representation, not from the formal precondition.
- Localization: generated theorem `is_prime_simple_entail_wit_1` in `coq/generated/is_prime_simple_goal.v`, and the active annotated C just before the loop invariant.
- Fix: added the bridge assertion while the local store still contains `n`:

```c
/*@ n <= INT_MAX by local */
```

- Result: the next regenerated `entail_wit_1` had the local-store permission on the left and no longer required proving the upper bound from the formal `Require` alone.

## Symexec invocation form

- Phenomenon: two initial manual `symexec` invocations failed before VC generation with:

```text
goal file not specified
Start to symbolic execution on program : (null)
```

- Trigger: this `symexec` binary accepts output and input path flags in `--flag=value` form; passing the path as a separate argv such as `--goal-file "$GEN/name_goal.v"` was not recognized.
- Localization: `logs/qcp_run.log` from the failed invocations.
- Fix: reran with the canonical form:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --goal-file="$GEN/is_prime_simple_goal.v" \
  --proof-auto-file="$GEN/is_prime_simple_proof_auto.v" \
  --proof-manual-file="$GEN/is_prime_simple_proof_manual.v" \
  --goal-check-file="$GEN/is_prime_simple_goal_check.v" \
  --input-file="$ANN" \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_180530_is_prime_simple \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --no-exec-info
```

- Result: the final `logs/qcp_run.log` ends with `Successfully finished symbolic execution` and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Manual return proofs

- Phenomenon: the generated `is_prime_simple_proof_manual.v` contained three manual placeholders:

```coq
proof_of_is_prime_simple_return_wit_1
proof_of_is_prime_simple_return_wit_2
proof_of_is_prime_simple_return_wit_3
```

- Trigger: these witnesses require unfolding the task-specific Coq spec and choosing the correct disjunct of `is_prime_simple_spec`.
- Localization: `output/verify_20260422_180530_is_prime_simple/coq/generated/is_prime_simple_proof_manual.v`.
- Fix: proved `return_wit_1` by contradiction with `n < 2`, `return_wit_2` by specializing the prime divisor condition at the discovered divisor `d`, and `return_wit_3` by constructing `is_prime_z n` from `2 <= n` plus the loop-exit universal remainder fact.
- Result: `is_prime_simple_proof_manual.v` contains no `Admitted.` and no top-level `Axiom` declaration.

## Proof script syntax fix

- Phenomenon: the first proof compile failed at `is_prime_simple_proof_manual.v` with:

```text
line 29, characters 22-24:
Error: Syntax error: ']' expected after [for_each_goal] (in [ltac_expr]).
```

- Trigger: the proof used the compact branch syntax `split; [reflexivity |].`, which parsed poorly under the generated file's local scopes.
- Localization: `logs/compile.log` and `coq/generated/is_prime_simple_proof_manual.v`.
- Fix: rewrote each conjunct proof with explicit bullets:

```coq
split.
- reflexivity.
- ...
```

and replaced an inline tactic argument in `return_wit_2` with a named assertion:

```coq
assert (Hd_range : 2 <= d < n_pre) by lia.
specialize (Hprime d Hd_range).
contradiction.
```

- Result: the next full compile passed through `is_prime_simple_goal_check.v`.

## Compile replay and cleanup

- Phenomenon: final success requires compiling the task-specific original Coq file and all generated files with the workspace logical prefix, then cleaning non-source artifacts.
- Trigger: the verify completion criteria require `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` to compile, `proof_manual.v` to contain no `Admitted.` or new `Axiom`, and workspace `coq/` plus `input/` to have no non-source intermediate files.
- Localization: compile log `output/verify_20260422_180530_is_prime_simple/logs/compile.log`; generated files under `coq/generated/`.
- Fix: compiled `original/is_prime_simple.v`, `is_prime_simple_goal.v`, `is_prime_simple_proof_auto.v`, `is_prime_simple_proof_manual.v`, and `is_prime_simple_goal_check.v` from `QualifiedCProgramming/SeparationLogic` using the documented load-path template; removed non-`.v` files under workspace `coq/` and non-`.c`/`.v` files under `input/`.
- Result: full compile exited with status 0, `goal_check.v` compiled, `proof_manual.v` has no `Admitted.` or `Axiom`, and cleanup checks returned no remaining non-source files under the required locations.
