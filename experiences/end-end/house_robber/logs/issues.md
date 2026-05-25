## 2026-04-22 17:20 +0800 - Fingerprint initially had empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` had `"semantic_description": ""` and `"keywords": {}` after workspace creation.
- Trigger: the verify skill requires an early nonempty semantic fingerprint and controlled-vocabulary keywords from `doc/retrieval/INDEX.md`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a description for the read-only array dynamic-programming scan. Keywords were selected only from the controlled vocabulary:

```json
{
  "algorithm_family": "dynamic_programming",
  "control_flow": "for_loop",
  "data_shape": "array",
  "semantic_intent": "preserve_input",
  "proof_pattern": ["loop_invariant", "case_split", "range_bound"],
  "numeric_properties": ["nonnegative_input", "overflow_guard", "int_range"],
  "edge_case_behavior": "empty_loop_possible"
}
```

- Result: the fingerprint is usable for retrieval and was later extended with `verification_status` after `goal_check.v` passed.

## 2026-04-22 17:22 +0800 - Missing loop invariant for house robber DP state

- Phenomenon: the active annotated file initially copied `input/house_robber.c` and had no `Inv` before the loop:

```c
for (i = 0; i < n; ++i) {
    take = prev2 + a[i];
    if (take > prev1) { cur = take; } else { cur = prev1; }
    prev2 = prev1;
    prev1 = cur;
}
```

- Trigger: the postcondition is stated with `house_robber_spec(l)`, but the C implementation maintains two scalar DP states. Without a loop invariant, symbolic execution cannot connect `prev1` at return to the Coq prefix specification or preserve the input array heap through the loop.
- Localization: `annotated/verify_20260422_171952_house_robber.c`, immediately before the `for (i = 0; i < n; ++i)` loop.
- Fix action: added a loop-head invariant preserving `a == a@pre`, `n == n@pre`, input length and bounds, the prefix-result bounds, `IntArray::full(a, n@pre, l)`, and the DP state:

```c
prev1 == house_robber_spec(sublist(0, i, l)) &&
((i == 0) => prev2 == 0) &&
((i > 0) => prev2 == house_robber_spec(sublist(0, i - 1, l))) &&
((i < n@pre) => prev2 + l[i] <= INT_MAX)
```

- Why this works: at loop head, `i` is the processed prefix length. `prev1` is the spec value for that prefix, while `prev2` is either the initial zero state at `i == 0` or the spec value for the prefix ending one element earlier. The guarded overflow assertion is needed before `take = prev2 + a[i]`.
- Result: rerunning `symexec` on the latest annotated file succeeded. `logs/qcp_run.log` ends with:

```text
Successfully finished symbolic execution
symexec_end=2026-04-22T17:22:28+08:00
symexec_elapsed=3
symexec_status=0
```

## 2026-04-22 17:24 +0800 - Manual proof obligations for prefix DP recurrence

- Phenomenon: fresh `symexec` generated five admitted manual obligations in `coq/generated/house_robber_proof_manual.v`:

```coq
proof_of_house_robber_safety_wit_4
proof_of_house_robber_entail_wit_1
proof_of_house_robber_entail_wit_2_1
proof_of_house_robber_entail_wit_2_2
proof_of_house_robber_return_wit_1
```

- Trigger: automation could not prove the pure recurrence relation between the two scalar DP states and `house_robber_spec (sublist 0 (i + 1) l)`, nor the derived next-iteration overflow guard.
- Localization: `coq/generated/house_robber_goal.v`, definitions `house_robber_safety_wit_4`, `house_robber_entail_wit_2_1`, `house_robber_entail_wit_2_2`, and `house_robber_return_wit_1`.
- Fix action: added local helper lemmas in `house_robber_proof_manual.v` using a proof-only state function `house_robber_state`. The central helper was:

```coq
Lemma house_robber_prefix_step :
  forall l i prev2 prev1,
    0 <= i ->
    i < Zlength l ->
    prev1 = house_robber_spec (sublist 0 i l) ->
    (i = 0 -> prev2 = 0) ->
    (i > 0 -> prev2 = house_robber_spec (sublist 0 (i - 1) l)) ->
    house_robber_spec (sublist 0 (i + 1) l) =
    Z.max (prev2 + Znth i l 0) prev1.
```

- Result: the generated recurrence and return witnesses became short calls to the helper lemmas plus `lia`.

## 2026-04-22 17:30 +0800 - `sac` scope interfered with ordinary Coq list proof syntax

- Phenomenon: the first manual proof compile failed before any generated witness proof:

```text
Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

and then singleton list notation failed with:

```text
The term "[x]" has type "?A -> Prop" while it is expected to have type "list ?A".
```

- Trigger: `Local Open Scope sac` was active before helper lemmas that used ordinary Coq proof syntax like `induction l as [| x xs IH]` and list notation `[x]`.
- Localization: `coq/generated/house_robber_proof_manual.v`, helper lemmas before the generated `proof_of_*` witnesses.
- Fix action: moved `Local Open Scope sac` below the helper lemmas and rewrote list singleton syntax as `x :: nil`. I also updated `experiences/general/PROOF.md` section 29 with this reusable rule.
- Result: helper lemmas parsed and compiled past the list syntax stage.

## 2026-04-22 17:33 +0800 - Preservation witness bullet order differed from the initial script

- Phenomenon: after `pre_process; entailer!`, the initial bullet scripts for `house_robber_entail_wit_2_1` and `house_robber_entail_wit_2_2` failed with errors such as:

```text
Wrong bullet -: Current bullet - is not finished.
Found no subterm matching "house_robber_spec (sublist 0 (i_2 + 1) l)"
```

- Trigger: the actual subgoal order was not the order guessed from reading the goal definition. After weakening the `cur` and `take` stack slots, Coq next asked for the next-overflow implication, then the shifted `prev2` implication, and only then the branch-specific equality.
- Localization: `proof_of_house_robber_entail_wit_2_1` and `proof_of_house_robber_entail_wit_2_2` in `coq/generated/house_robber_proof_manual.v`.
- Fix action: used a temporary `Show.` probe to inspect the real proof state. Reordered the bullets and weakened both temporary stack slots with:

```coq
sep_apply store_int_undef_store_int.
sep_apply store_int_undef_store_int.
entailer!.
```

- Result: both preservation witnesses compiled. The final `proof_manual.v` contains no `Admitted.` and no added `Axiom`.

## 2026-04-22 17:36 +0800 - Full Coq chain and cleanup

- Phenomenon: verification is not complete after `symexec` or isolated manual proof compilation; the full generated Coq chain must compile and intermediate build artifacts must be removed.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented load-path template:

```text
compiled=original/house_robber.v:success
compiled=house_robber_goal.v:success
compiled=house_robber_proof_auto.v:success
compiled=house_robber_proof_manual.v:success
compiled=house_robber_goal_check.v:success
```

- Cleanup action: deleted all non-`.v` files under `output/verify_20260422_171952_house_robber/coq/` and checked that `input/` had no non-`.c`/non-`.v` intermediates.
- Result: `goal_check.v` passed, `proof_manual.v` has no `Admitted.` or top-level `Axiom`, and `find output/verify_20260422_171952_house_robber/coq -type f ! -name '*.v'` prints no files.
