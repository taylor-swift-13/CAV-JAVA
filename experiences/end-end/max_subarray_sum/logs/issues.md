# Issues: max_subarray_sum verify

## 2026-04-22 - Workspace fingerprint initially had empty retrieval fields

- Phenomenon: `logs/workspace_fingerprint.json` had `"semantic_description": ""` and an empty `keywords` object.
- Trigger: the verify workspace was initialized before semantic classification.
- Localization: `output/verify_20260422_192331_max_subarray_sum/logs/workspace_fingerprint.json`.
- Fix action: read the repository-level `doc/retrieval/INDEX.md` because the current workspace did not contain `doc/retrieval/INDEX.md`, then filled the semantic description and used only controlled vocabulary keys and values. The initial verification status was `manual_witness_needed`; after final compile it was extended to include `goal_check_passed`, `proof_check_passed`, `auto_proof_contains_admitted`, and `generated_goal_contains_axioms`.
- Result: the fingerprint is non-empty and usable for future retrieval.

## 2026-04-22 - Loop invariant needed both accumulator semantics and an overflow bridge

- Phenomenon: the input C had no loop invariant for the Kadane scan:

```c
for (i = 1; i < n; ++i) {
    if (cur + a[i] < a[i]) {
        cur = a[i];
    } else {
        cur = cur + a[i];
    }
    if (best < cur) {
        best = cur;
    }
}
```

- Trigger: the postcondition is stated through `max_subarray_sum_spec(l)`, while the C loop updates two state variables. The C expression `cur + a[i]` also requires a signed-int range proof before the branch can be symbolically executed.
- Localization: active annotated file `annotated/verify_20260422_192331_max_subarray_sum.c`.
- Fix action: added `Extern Coq (max_subarray_sum_acc : Z -> Z -> list Z -> Z)` and a loop invariant with:

```c
exists lo,
  1 <= i && i <= n &&
  n == n@pre &&
  a == a@pre &&
  n@pre == Zlength(l) &&
  0 <= lo && lo < i &&
  cur == sum(sublist(lo, i, l)) &&
  INT_MIN <= cur && cur <= INT_MAX &&
  INT_MIN <= best && best <= INT_MAX &&
  max_subarray_sum_acc(cur, best, sublist(i, n, l)) ==
    max_subarray_sum_spec(l) &&
  IntArray::full(a, n, l)
```

- Result: `symexec` completed successfully and generated fresh `max_subarray_sum_goal.v`, `max_subarray_sum_proof_auto.v`, `max_subarray_sum_proof_manual.v`, and `max_subarray_sum_goal_check.v`.

## 2026-04-22 - Fresh symexec generated eight manual obligations

- Phenomenon: after successful symbolic execution, `coq/generated/max_subarray_sum_proof_manual.v` contained eight `Admitted.` placeholders:

```coq
proof_of_max_subarray_sum_safety_wit_4
proof_of_max_subarray_sum_safety_wit_5
proof_of_max_subarray_sum_entail_wit_1
proof_of_max_subarray_sum_entail_wit_2_1
proof_of_max_subarray_sum_entail_wit_2_2
proof_of_max_subarray_sum_entail_wit_2_3
proof_of_max_subarray_sum_entail_wit_2_4
proof_of_max_subarray_sum_return_wit_1
```

- Trigger: the remaining VCs are pure list/arithmetic obligations: singleton subarray sums, extending a subarray by one element, unfolding one accumulator step, and normalizing `Z.max` according to the C branch facts.
- Localization: `output/verify_20260422_192331_max_subarray_sum/coq/generated/max_subarray_sum_proof_manual.v`.
- Fix action: added local helper lemmas `sublist_head_cons_Z`, `sum_sublist_single_Z`, `sum_sublist_snoc_Z`, `max_subarray_sum_spec_nonempty_acc`, and `max_subarray_sum_acc_step_cons`, plus small Ltac helpers to instantiate the overflow guard. The branch witnesses then rewrite the suffix as `Znth i l 0 :: sublist (i + 1) n_pre l`, simplify one accumulator step, and replace `Z.max` using the branch inequalities.
- Result: all manual witnesses compile, and `rg -n "Admitted\\.|^\\s*Axiom\\b|^\\s*Parameter\\b" max_subarray_sum_proof_manual.v` returns no matches.

## 2026-04-22 - Helper proof side condition used the wrong `Zlength_correct` rewrite shape

- Phenomenon: the first compile replay failed in `sum_sublist_snoc_Z`:

```text
File ".../max_subarray_sum_proof_manual.v", line 55:
Error: Found no subterm matching "Zlength ?M2995" in the current goal.
```

- Trigger: the side condition for `sublist_split` was phrased in terms of `Z.of_nat (length l)`, so `rewrite Zlength_correct` had no direct target.
- Fix action: changed the side-condition proof from:

```coq
rewrite (sublist_split lo (i + 1) i l) by (rewrite Zlength_correct; lia).
```

to:

```coq
rewrite (sublist_split lo (i + 1) i l) by (pose proof Zlength_correct l; lia).
```

- Result: the helper lemma compiled.

## 2026-04-22 - Generated proof scopes rejected `destruct l as ...`

- Phenomenon: the second compile replay failed with:

```text
Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

- Trigger: under the generated proof file's open scopes, `destruct l as [| x xs]` was parsed unstably.
- Fix action: changed the helper proof to use `destruct l.` as in nearby successful examples.
- Result: the nonempty-spec helper compiled.

## 2026-04-22 - Manual witness bullet order differed from assertion text order

- Phenomenon: several proof attempts failed with unification errors or `Cannot find witness`, for example:

```text
Unable to unify "max_subarray_sum_spec l" with
"max_subarray_sum_acc (sum (sublist i (i + 1) l))
   (sum (sublist i (i + 1) l)) (sublist (i + 1) n_pre l)".
```

and:

```text
Tactic failure: Cannot find witness.
```

- Trigger: after `entailer!`, the pure subgoals did not follow the textual order in the generated assertion. For `entail_wit_1`, the accumulator equation appeared before the singleton-sum equality and range goals. For branch witnesses, some range facts were discharged automatically from branch inequalities and invariant bounds, while others required explicit overflow-guard instantiation.
- Fix action: inspected the proof states with `coqtop Show`, then reordered bullets per witness. The final scripts prove accumulator equations first, then only the needed range goals, and prove singleton or snoc sum equalities last.
- Result: `max_subarray_sum_proof_manual.v` compiled.

## 2026-04-22 - Full compile and cleanup required after proof success

- Phenomenon: successful `symexec` and manual proof compilation are not enough for Verify success. The complete generated chain must compile and build byproducts must be removed.
- Trigger: Coq compilation produced `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under the workspace `coq/` tree, and compiling `original/max_subarray_sum.v` produced `input/.max_subarray_sum.aux`.
- Fix action: compiled `original/max_subarray_sum.v`, `max_subarray_sum_goal.v`, `max_subarray_sum_proof_auto.v`, `max_subarray_sum_proof_manual.v`, and `max_subarray_sum_goal_check.v` with the documented load paths. Then deleted all non-`.v` files under `output/verify_20260422_192331_max_subarray_sum/coq/` and all non-`.c`/non-`.v` files under `input/`.
- Result: `goal_check.v` compiled successfully, `proof_manual.v` contains no `Admitted.` or added `Axiom`, and cleanup checks print no remaining intermediate files.
