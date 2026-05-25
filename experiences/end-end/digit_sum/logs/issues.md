## Fingerprint initially had empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` had an empty `semantic_description` and `{}` keywords.
- Trigger: the verify workflow requires this to be filled early, after reading `doc/retrieval/INDEX.md`.
- Fix action: read the retrieval index and updated the fingerprint with a nonempty description of the scalar digit-sum loop. The keyword keys and values were chosen only from the controlled vocabulary: `algorithm_family=accumulation`, `control_flow=while_loop`, `data_shape=scalar_only`, `semantic_intent=preserve_input`, `proof_pattern=[loop_invariant,pure_arithmetic,termination_by_bound]`, `numeric_properties=[nonnegative_input,monotone_accumulator]`, `edge_case_behavior=empty_loop_possible`.
- Result: the fingerprint now has usable semantic retrieval metadata. Final status keywords were later updated to include `manual_witness_needed` and `auto_proof_contains_admitted`.

## Initial loop invariant was too weak for addition safety

- Phenomenon: after the first successful `symexec`, `digit_sum_safety_wit_3` required proving:

```coq
sum + n % 10 <= INT_MAX
```

but the invariant provided only:

```coq
0 <= sum
sum <= n_pre
sum + digit_sum_z n = digit_sum_z n_pre
0 <= n_pre
```

- Localization: active annotated C immediately before `while (n > 0)` in `annotated/verify_20260422_154652_digit_sum.c`.
- Fix action: strengthened the invariant from `sum <= n@pre` to `sum + n <= n@pre`, because for positive `n`, `0 <= n % 10 <= n`, so the next addition is bounded by the remaining numeric state.
- Result: regenerated goals included the stronger fact `sum + n <= n_pre`, which is the right arithmetic bridge for `sum += n % 10`.

## Current input contract does not expose the C int upper bound

- Phenomenon: even with the strengthened invariant, the safety proof still needed an upper bound for the original input. The distilled upper-bound chain is:

```coq
sum + n % 10 <= sum + n <= n_pre <= INT_MAX
```

but the input contract only provides:

```c
/*@ Require
      0 <= n && emp
*/
```

so generated Coq contexts contain `0 <= n_pre` but not `n_pre <= INT_MAX`.
- Trigger: trying to carry `n@pre <= INT_MAX` in the loop invariant.
- Localization: generated `digit_sum_entail_wit_1` after the bridge assertion:

```coq
Definition digit_sum_entail_wit_1 :=
forall (n_pre: Z),
  [| (0 <= n_pre) |] && emp
|--
  [| (n_pre <= INT_MAX) |] &&
  [| (0 = 0) |] &&
  emp.
```

- Why this is a blocker: the proposition `forall n_pre, 0 <= n_pre -> n_pre <= INT_MAX` is false over `Z`; for example `n_pre = INT_MAX + 1` satisfies the precondition but not the desired upper bound. This is not a missing tactic or helper lemma.
- Fix action attempted inside Verify: added a small bridge assertion before the loop to preserve `n == n@pre`, `n@pre <= INT_MAX`, and `sum == 0`; this preserved local permissions but still generated the false pure obligation above because the formal `Require` does not include the upper bound.
- Result: verification cannot soundly succeed in Verify without a Contract-stage change such as adding `n <= INT_MAX` to the formal precondition. I did not edit `input/digit_sum.c` or rewrite the annotated `Require`, because the Verify workflow forbids changing the contract.

## Bridge assertion initially dropped the `sum` local permission

- Phenomenon: the first bridge assertion mentioned only `n == n@pre` and `n@pre <= INT_MAX`; `symexec` failed at the following loop invariant with:

```text
Partial Solve Invariant Error in .../annotated/verify_20260422_154652_digit_sum.c:26:4
Sep cannot be fully solved
The Sep is:
SEP[store(sum_67_addr , sum_76_value , signed int)]
```

- Cause: the assertion did not mention `sum`, so the partial solver did not preserve the `sum` local permission across the assertion before the loop invariant.
- Fix action: changed the bridge assertion to:

```c
/*@ Assert
      n == n@pre &&
      n@pre <= INT_MAX &&
      sum == 0
*/
```

- Result: `symexec` succeeded after the assertion retained both local stores, but the proof remained blocked by the missing input upper-bound contract described above.

## Archived `digit_sum` proof used `Z.quot`, current spec uses `Z.div`

- Phenomenon: adapting the archived exact `digit_sum` proof initially failed in `digit_sum_fuel_stable` with:

```text
Found no subterm matching "digit_sum_fuel (n ÷ 10) (fuel + extra)"
```

- Cause: the archived proof was for a `digit_sum.v` whose recursive call used `Z.quot n 10`, while the current input file defines:

```coq
else Z.rem n 10 + digit_sum_fuel (Z.div n 10) k
```

- Fix action: changed the helper proof plan to recurse over `n / 10` for the spec, keep `n ÷ 10` for generated C goals, and bridge them with `Z.quot_div_nonneg` under nonnegative operands.
- Result: this proof adaptation is viable, but the task still cannot complete because of the separate contract upper-bound gap.

## Compile replay must fail fast

- Phenomenon: an early compile replay continued after `digit_sum_proof_manual.v` failed, then also reported that `goal_check.v` could not find `digit_sum_proof_manual`.
- Cause: the shell compile block did not use `set -e`, so later `coqc` commands ran after the first failure.
- Fix action: reran compile checks with `set -e`, so the log stops at the first real proof failure.
- Result: subsequent compile logs report the actual first failing proof obligation rather than a cascade error.

## Retry confirmed upper-bound gap after removing the false bridge assertion

- Phenomenon: the previous run's explicit bridge assertion:

```c
/*@ Assert
      n == n@pre &&
      n@pre <= INT_MAX &&
      sum == 0
*/
```

generated the false witness `forall n_pre, 0 <= n_pre -> n_pre <= INT_MAX`. This retry removed that assertion and changed the invariant in `annotated/verify_20260422_154652_digit_sum.c` to carry the direct live-state safety bound:

```c
/*@ Inv
      0 <= n &&
      0 <= sum &&
      sum + n <= n@pre &&
      sum + n <= INT_MAX &&
      sum + digit_sum_z(n) == digit_sum_z(n@pre)
*/
```

- Trigger: `symexec` was rerun after the annotation change and succeeded, but the regenerated `coq/generated/digit_sum_goal.v` still contains an unprovable loop-entry obligation:

```coq
Definition digit_sum_entail_wit_1 :=
forall (n_pre: Z),
  [| (0 <= n_pre) |] && emp
|--
  ...
  [| ((0 + n_pre ) <= INT_MAX) |] &&
  ...
  emp.
```

- Cause: any invariant strong enough to prove C signed-int safety for `sum += n % 10` needs an initial upper bound on the original argument. The formal contract in `input/digit_sum.c` still only provides:

```c
/*@ Require
      0 <= n && emp
*/
```

so `0 + n_pre <= INT_MAX` is false for arbitrary mathematical `Z` values satisfying `0 <= n_pre`.

- Fix action attempted inside Verify: removed the self-created false pure assertion and tried to rely on the typed local `int` state by carrying `sum + n <= INT_MAX` directly. This avoided the old `n_pre <= INT_MAX` assertion witness but still produced the equivalent pure entry VC above after loop-invariant initialization.

- Result: the precise blocker is confirmed as a Contract-stage precondition gap, not a missing Coq tactic. Verification cannot soundly finish unless the input contract is strengthened, for example with `n <= INT_MAX`, or the function/specification is otherwise adjusted by the Contract stage. The retry did not edit `input/digit_sum.c` and did not add any `Axiom`.

## Local int upper bound should use `by local`, not a pure bridge assertion

- Phenomenon: the earlier retries treated `n@pre <= INT_MAX` as an unprovable contract gap because both a pure bridge assertion and the invariant entry condition generated obligations of the form:

```coq
forall n_pre : Z, 0 <= n_pre -> n_pre <= INT_MAX
```

- Trigger: the active annotation tried to carry `n@pre <= INT_MAX` as an ordinary pure assertion or tried to initialize `sum + n <= INT_MAX` after local stores had been abstracted away.
- Localization: the repaired active file `annotated/verify_20260422_154652_digit_sum.c` now places the local extraction immediately after `int sum = 0` and before the loop:

```c
/*@ n <= INT_MAX by local */
```

- Fix action: add the `by local` annotation and carry `n@pre <= INT_MAX` in the loop invariant:

```c
/*@ Inv
      0 <= n &&
      0 <= sum &&
      n@pre <= INT_MAX &&
      sum + n <= n@pre &&
      sum + digit_sum_z(n) == digit_sum_z(n@pre)
*/
```

- Result: fresh `symexec` succeeded and `digit_sum_entail_wit_1` now has local `Int` stores on the left side:

```coq
[| (0 <= n_pre) |]
&& ((( &( "sum" ) )) # Int |-> 0)
** ((( &( "n" ) )) # Int |-> n_pre)
|-- [| (n_pre <= INT_MAX) |] && ...
```

This is soundly discharged by the generated proof infrastructure, so the task moved from a false pure obligation to normal manual proof obligations.

## Current `digit_sum_z` spec recurses with `Z.div`, while generated C goals use `Z.quot`

- Phenomenon: adapting the archived digit-sum proof failed at quotient/division rewrite points. The first compile error was:

```text
Unable to unify "? ÷ ? = ? / ?" with "n / 10 = n ÷ 10".
```

- Cause: `input/digit_sum.v` defines:

```coq
else Z.rem n 10 + digit_sum_fuel (Z.div n 10) k
```

but generated C goals use `n ÷ 10` for C integer division.
- Fix action: prove `digit_sum_fuel_stable` over `n / 10`, prove `quot_10_lt_pos` for generated goals, and bridge nonnegative division with `Z.quot_div_nonneg`. The two `replace` sites need opposite orientations: `quot_10_lt_pos` needs `symmetry`, while `digit_sum_z_step` does not.
- Result: `digit_sum_z_step` compiles in the current workspace and supports the loop-preservation witness:

```coq
digit_sum_z n = Z.rem n 10 + digit_sum_z (n ÷ 10)
```

## Entailer bullet order and return witness needed explicit pure cleanup

- Phenomenon: after helper lemmas compiled, `proof_of_digit_sum_entail_wit_3` failed because the first bullet tried to prove quotient nonnegativity while the actual first subgoal was:

```coq
sum + n % 10 + digit_sum_z (n ÷ 10) = digit_sum_z n_pre
```

- Fix action: reorder the `entailer!` bullets so the semantic equation is proved first using `rewrite <- H4` and `digit_sum_z_step`; then discharge the quotient/rem arithmetic bullets.
- Phenomenon: the return witness also failed with an incomplete proof. `coqtop` showed the remaining goal:

```coq
H : n <= 0
H0 : 0 <= n
H4 : sum + digit_sum_z n = digit_sum_z n_pre
============================
sum = digit_sum_z n_pre
```

- Fix action: explicitly derive `n = 0`, unfold `digit_sum_z 0`, and finish with `lia`.
- Result: `digit_sum_proof_manual.v` compiles without `Admitted.` or top-level `Axiom`.

## Final compile and cleanup succeeded

- Trigger: final verification requires `original/digit_sum.v`, `digit_sum_goal.v`, `digit_sum_proof_auto.v`, `digit_sum_proof_manual.v`, and `digit_sum_goal_check.v` to compile with the workspace load path.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented `BASE` load path, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_154652_digit_sum`.
- Result: `logs/compile_full.log` records:

```text
compiled original
compiled goal
compiled proof_auto
compiled proof_manual
compiled goal_check
```

Afterward, all non-`.v` files under `output/verify_20260422_154652_digit_sum/coq` were deleted, and `input/` had no non-`.c`/non-`.v` intermediates.
