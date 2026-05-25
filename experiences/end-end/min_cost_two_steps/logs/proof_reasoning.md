## 2026-04-22 20:26 +0800 - Manual witness plan after successful symexec

Fresh `symexec` succeeded on `annotated/verify_20260422_201546_min_cost_two_steps.c` and generated non-empty Coq artifacts in this workspace.  The generated `coq/generated/min_cost_two_steps_proof_manual.v` contains seven admitted manual witnesses:

```coq
proof_of_min_cost_two_steps_safety_wit_4
proof_of_min_cost_two_steps_safety_wit_8
proof_of_min_cost_two_steps_safety_wit_9
proof_of_min_cost_two_steps_entail_wit_1
proof_of_min_cost_two_steps_entail_wit_2_1
proof_of_min_cost_two_steps_entail_wit_2_2
proof_of_min_cost_two_steps_return_wit_2
```

The safety witnesses are arithmetic obligations.  `safety_wit_4` proves the initialization addition `Znth 0 l 0 + Znth 1 l 0` is an `int`; it should follow from `n_pre <> 1`, `1 <= n_pre`, nonnegative elements, and the prefix-sum bound for `k = 2`.  `safety_wit_8` and `safety_wit_9` prove the branch additions in the loop; their left side already contains branch-sensitive guarded overflow facts from the invariant, so after `pre_process` and `entailer!` they should reduce to applying those implications plus nonnegativity.

The entailment witnesses require pure list/DP helper lemmas.  The important generated targets are:

```coq
prev2 = min_cost_two_steps_spec (sublist 0 (i_2 - 1) l)
prev1 = min_cost_two_steps_spec (sublist 0 i_2 l)
```

and after one loop body they must establish:

```coq
prev1 = min_cost_two_steps_spec (sublist 0 (i_2 + 1 - 1) l)
Z.min prev1 prev2 + Znth i_2 l 0 =
  min_cost_two_steps_spec (sublist 0 (i_2 + 1) l)
```

I will add local helper lemmas directly in `min_cost_two_steps_proof_manual.v` before the generated witnesses.  The helpers will define a proof-only state function for `min_cost_two_steps_acc`, prove a prefix step recurrence

```coq
min_cost_two_steps_spec (sublist 0 (i + 1) l) =
  Z.min (min_cost_two_steps_spec (sublist 0 i l))
        (min_cost_two_steps_spec (sublist 0 (i - 1) l)) +
  Znth i l 0
```

for `2 <= i < Zlength l`, and prove a prefix upper bound

```coq
0 <= min_cost_two_steps_spec (sublist 0 k l) /\
min_cost_two_steps_spec (sublist 0 k l) <= sum (sublist 0 k l)
```

from nonnegative input elements.  Those helpers are enough for the two preservation witnesses and for the guarded overflow facts needed by the next loop iteration.  The return witness then only needs `i_2 = n_pre` and `sublist 0 n_pre l = l`.
