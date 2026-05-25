## 2026-04-22 18:56 +0800 - Workspace fingerprint was still placeholder metadata

- Phenomenon: `logs/workspace_fingerprint.json` had an empty `semantic_description` and an empty `keywords` object:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the verify workflow requires reading `doc/retrieval/INDEX.md` early and filling the fingerprint with controlled vocabulary before verification continues.
- Localization: `output/verify_20260422_185520_lower_bound/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, described the target as a read-only lower-bound binary search over a sorted integer array, and filled only controlled key/value terms such as `algorithm_family: search`, `control_flow: while_loop`, `data_shape: array`, `semantic_intent: preserve_input`, and proof patterns including `loop_invariant`, `case_split`, `termination_by_bound`, `range_bound`, and `monotonicity`.
- Result: the fingerprint became usable for retrieval. After final verification, `verification_status` was updated to `["goal_check_passed", "proof_check_passed"]`.

## 2026-04-22 18:56 +0800 - Missing lower-bound invariant and midpoint bridge

- Phenomenon: the active annotated C initially had the bare loop with no `Inv` or post-midpoint `Assert`:

```c
while (left < right) {
    mid = left + (right - left) / 2;
    if (a[mid] < target) {
        left = mid + 1;
    } else {
        right = mid;
    }
}
```

- Trigger: the postcondition of `lower_bound` requires two global facts at return time:

```c
(forall (i: Z), (0 <= i && i < __return) => l[i] < target) &&
(forall (i: Z), (__return <= i && i < n) => target <= l[i])
```

Without an invariant, symbolic execution has no persistent record that `[0,left)` is already below `target` and `[right,n)` is already at least `target`.
- Localization: `annotated/verify_20260422_185520_lower_bound.c`, immediately before and inside the `while (left < right)` loop.
- Fix action: added the half-open binary-search invariant:

```c
/*@ Inv
      0 <= n &&
      n <= INT_MAX &&
      Zlength(l) == n &&
      (forall (i: Z) (j: Z),
        (0 <= i && i <= j && j < n) => l[i] <= l[j]) &&
      0 <= left && left <= right && right <= n &&
      a == a@pre &&
      n == n@pre &&
      target == target@pre &&
      (forall (i: Z), (0 <= i && i < left) => l[i] < target) &&
      (forall (i: Z), (right <= i && i < n) => target <= l[i]) &&
      IntArray::full(a, n, l)
*/
```

and added a bridge assertion after computing `mid` to expose:

```c
0 <= mid && mid < n &&
left <= mid && mid < right
```

with the sortedness, prefix, suffix, and `IntArray::full` facts still available.
- Result: `symexec` succeeded and generated five manual witnesses: midpoint arithmetic, invariant initialization, midpoint assertion, and the two branch-preservation obligations.

## 2026-04-22 18:57 +0800 - Manual proof obligations for midpoint and sorted-branch preservation

- Phenomenon: `coq/generated/lower_bound_proof_manual.v` initially contained five admitted lemmas:

```coq
Lemma proof_of_lower_bound_safety_wit_2 : lower_bound_safety_wit_2.
Proof. Admitted.
...
Lemma proof_of_lower_bound_entail_wit_3_2 : lower_bound_entail_wit_3_2.
Proof. Admitted.
```

- Trigger: the generated VCs require quotient bounds for `(right-left) ÷ 2` and sortedness reasoning to preserve the two quantified invariant regions after each branch.
- Localization: `output/verify_20260422_185520_lower_bound/coq/generated/lower_bound_proof_manual.v`.
- Fix action: added a local helper:

```coq
Lemma lower_bound_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
```

Then proved:

- `proof_of_lower_bound_safety_wit_2` by extracting `left` and `right` local `Int` ranges with `store_int_range`, applying `lower_bound_quot2_bounds`, and finishing with `entailer!`.
- `proof_of_lower_bound_entail_wit_1` with `pre_process`, because both initial quantified regions are empty.
- `proof_of_lower_bound_entail_wit_2` using the quotient helper plus `Z.quot_lt` for the strict midpoint upper bound.
- `proof_of_lower_bound_entail_wit_3_1` by proving the new suffix fact `forall j, mid <= j < n_pre -> target_pre <= Znth j l 0`; `j = mid` uses the branch condition, and `j > mid` uses sortedness.
- `proof_of_lower_bound_entail_wit_3_2` by proving the new prefix fact `forall j, 0 <= j < mid + 1 -> Znth j l 0 < target_pre`; old-prefix indices reuse the invariant, and indices through `mid` use sortedness into `l[mid] < target`.

- Result: `lower_bound_proof_manual.v` compiled successfully, and `rg -n "Admitted\\.|^\\s*Axiom\\b" lower_bound_proof_manual.v` returned no matches.

## 2026-04-22 18:58 +0800 - Full Coq compile replay and cleanup

- Phenomenon: verification is not complete until generated `goal`, `proof_auto`, `proof_manual`, and `goal_check` compile together with the current workspace load path, and compile artifacts are removed afterward.
- Trigger: normal verify completion criteria.
- Localization: `output/verify_20260422_185520_lower_bound/coq/generated/`.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the standard base `-R` paths and:

```bash
-Q output/verify_20260422_185520_lower_bound/original ""
-R output/verify_20260422_185520_lower_bound/coq/generated SimpleC.EE.CAV.verify_20260422_185520_lower_bound
```

The compile order was:

```text
lower_bound_goal.v
lower_bound_proof_auto.v
lower_bound_proof_manual.v
lower_bound_goal_check.v
```

- Result: all four files compiled successfully. After `find output/verify_20260422_185520_lower_bound/coq -type f ! -name '*.v' -delete`, a follow-up `find` reported no remaining non-`.v` Coq artifacts. There was no workspace `input/` cleanup needed.
