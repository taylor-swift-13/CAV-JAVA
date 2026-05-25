## Fingerprint initialized from controlled retrieval vocabulary

- Phenomenon: the initial `logs/workspace_fingerprint.json` had an empty `semantic_description` and empty `keywords`, which violates the verify workflow requirement for early retrieval metadata.
- Trigger: this workspace was created with only `original/`, empty `coq/`, and the placeholder fingerprint.  The requested workflow explicitly required reading `doc/retrieval/INDEX.md` early, even though the workspace did not have a local `doc/retrieval/INDEX.md` copy.
- Localization: `output/verify_20260422_201546_min_cost_two_steps/logs/workspace_fingerprint.json`.
- Fix action: read the project-level `doc/retrieval/INDEX.md` and filled a non-empty semantic description.  Used only controlled keys and values, including `algorithm_family: dynamic_programming`, `control_flow: [if, for_loop]`, `data_shape: array`, `semantic_intent: preserve_input`, and proof patterns `loop_invariant`, `case_split`, `range_bound`, and `pure_arithmetic`.
- Result: the fingerprint is usable for retrieval and was later updated to `verification_status: [goal_check_passed, proof_check_passed]` after successful full compile.

## Missing loop invariant for rolling two-state DP

- Phenomenon: the active annotated C initially matched `input/min_cost_two_steps.c` and had no `Inv` before the `for (i = 2; i < n; ++i)` loop.  Without a loop invariant, the verifier would not have a summary relating `prev2` and `prev1` to `min_cost_two_steps_spec(l)`.
- Trigger: the function computes a prefix dynamic-programming recurrence using two scalar states.  The postcondition needs `__return == min_cost_two_steps_spec(l)`, while the loop body only updates local scalars.
- Localization: `annotated/verify_20260422_201546_min_cost_two_steps.c`, loop before `for (i = 2; i < n; ++i)`.
- Fix action: added an invariant where `i` is the next index to consume, `prev2 == min_cost_two_steps_spec(sublist(0, i - 1, l))`, `prev1 == min_cost_two_steps_spec(sublist(0, i, l))`, `cost == cost@pre`, `n == n@pre`, array length and element bounds are preserved, and `IntArray::full(cost, n@pre, l)` is carried through the loop.
- Refinement: the first invariant included branch-sensitive future-overflow implications.  After inspecting the generated preservation witnesses, those were removed and replaced with a state-independent forall bound:

```c
(forall (k: Z),
  (1 <= k && k <= n@pre) =>
  (0 <= min_cost_two_steps_spec(sublist(0, k, l)) &&
   min_cost_two_steps_spec(sublist(0, k, l)) <= sum(sublist(0, k, l))))
```

- Result: `symexec` succeeded on the final annotated file and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.  The final `logs/qcp_run.log` ends with `Successfully finished symbolic execution` and `symexec_status=0`.

## Manual proof required DP recurrence and prefix-bound helpers

- Phenomenon: fresh `coq/generated/min_cost_two_steps_proof_manual.v` contained seven admitted manual witnesses: `safety_wit_4`, `safety_wit_8`, `safety_wit_9`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, and `return_wit_2`.
- Trigger: the generated VCs needed pure Coq facts not available to `proof_auto.v`: a recurrence for extending a nonempty prefix by one cost, a proof-only state relation for `min_cost_two_steps_acc`, and a bound showing the DP value of every nonempty prefix is between `0` and that prefix's `sum`.
- Localization: `output/verify_20260422_201546_min_cost_two_steps/coq/generated/min_cost_two_steps_proof_manual.v`.
- Fix action: added local helper lemmas, including `min_cost_two_steps_state`, `min_cost_two_steps_prefix_step`, `min_cost_two_steps_acc_bound`, `min_cost_two_steps_prefix_bound`, and `min_cost_two_steps_full_sublist`.  The branch witnesses then use `min_cost_two_steps_prefix_step` plus `Z.min_l`/`Z.min_r`, and the return witness uses `sublist_self` through `min_cost_two_steps_full_sublist`.
- Representative Coq proof shape:

```coq
rewrite (min_cost_two_steps_prefix_step l i_2) by lia.
subst prev1 prev2.
rewrite Z.min_l by lia.
reflexivity.
```

- Result: `rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/min_cost_two_steps_proof_manual.v` returns no matches, and `proof_manual.v` compiles.

## Coq proof iteration pitfalls fixed

- Phenomenon: several initial helper scripts failed during `coqc`, even though the proof ideas were correct.
- Trigger and fixes:
  - `sublist_single` did not rewrite goals written as `sublist 0 1 l`; fixed by replacing the upper bound with `0 + 1` or by using `symmetry; apply sublist_single`.
  - `induction xs as [| x xs IH]` produced a parser error in this proof context; fixed by using `induction xs` and the generated names.
  - `Znth` over cons lists needed explicit `Znth0_cons` and `Znth_cons` rewrites instead of relying on `simpl`.
  - `entailer!` produced pure subgoals in reverse order from the first guessed script for `safety_wit_4`, `entail_wit_1`, and the two loop preservation witnesses; fixed by inspecting proof states and reordering bullets.
- Result: the final fail-fast compile log records successful compilation of `original`, `goal`, `proof_auto`, `proof_manual`, and `goal_check`.

## Full compile and cleanup completed

- Phenomenon: successful `symexec` and manual proof are not sufficient for Verify success; the generated Coq chain must compile through `goal_check.v`, and non-`.v` build artifacts must be removed.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` load paths, `-Q "$ORIG" ""`, and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_201546_min_cost_two_steps`.  After success, removed non-`.v` files under `coq/`, removed Coq artifacts produced under `original/`, and checked that `input/` had no non-`.c`/`.v` intermediates.
- Result: `min_cost_two_steps_goal_check.v` compiled successfully.  `proof_manual.v` contains no `Admitted.` and no top-level `Axiom`.
