## 2026-04-23 05:26 CST - Manual proof plan after successful symexec

Fresh `symexec` succeeded on the latest active annotated file and generated `tribonacci_goal.v`, `tribonacci_proof_auto.v`, `tribonacci_proof_manual.v`, and `tribonacci_goal_check.v`. The generated manual proof file contains six admitted obligations:

```coq
Lemma proof_of_tribonacci_safety_wit_9 : tribonacci_safety_wit_9.
Lemma proof_of_tribonacci_safety_wit_10 : tribonacci_safety_wit_10.
Lemma proof_of_tribonacci_entail_wit_1 : tribonacci_entail_wit_1.
Lemma proof_of_tribonacci_entail_wit_2 : tribonacci_entail_wit_2.
Lemma proof_of_tribonacci_return_wit_1 : tribonacci_return_wit_1.
Lemma proof_of_tribonacci_return_wit_2 : tribonacci_return_wit_2.
```

The relevant generated goals are scalar-only. `tribonacci_safety_wit_9` must prove `((a + b) + c)` is in the C `int` range under `3 <= i <= n_pre <= 37` and the invariant equalities `a = tribonacci_z (i - 3)`, `b = tribonacci_z (i - 2)`, and `c = tribonacci_z (i - 1)`. `tribonacci_safety_wit_10` is the same range check for the subexpression `a + b`. `tribonacci_entail_wit_2` is invariant preservation after `d = a + b + c; a = b; b = c; c = d; ++i`; its only heap side condition is weakening `&( "d") # Int |-> ((a + b) + c)` to `&( "d") # Int |-_`, and its pure side condition is the recurrence equality `tribonacci_z i = tribonacci_z (i - 3) + tribonacci_z (i - 2) + tribonacci_z (i - 1)`.

Reusable pattern: `examples/fibonacci/coq/generated/fibonacci_proof_manual.v` has the same scalar recurrence shape. It uses a small bounded case-splitting tactic, helper lemmas for the recurrence and C `int` bounds, and `StoreAux.store_int_undef_store_int` for weakening the temporary variable store. I will use the same structure, adjusted to the Tribonacci recurrence and bound `n <= 37`.

Planned proof shape:

```coq
From SimpleC.SL Require Import Mem SeparationLogic StoreAux.

Lemma tribonacci_z_sum_int_bound_3_37 :
  forall i, 3 <= i -> i <= 37 ->
    INT_MIN <= (tribonacci_z (i - 3) + tribonacci_z (i - 2)) + tribonacci_z (i - 1) <= INT_MAX.

Lemma tribonacci_z_pair_sum_int_bound_3_37 :
  forall i, 3 <= i -> i <= 37 ->
    INT_MIN <= tribonacci_z (i - 3) + tribonacci_z (i - 2) <= INT_MAX.

Lemma tribonacci_z_step_3_37 :
  forall i, 3 <= i -> i <= 37 ->
    (tribonacci_z (i - 3) + tribonacci_z (i - 2)) + tribonacci_z (i - 1) = tribonacci_z i.
```

The helpers are finite arithmetic facts over the contract's bounded range and can be discharged by destructing `i` from `0` through `37` and reducing `tribonacci_z`. The main witness proofs should then be short: `pre_process`, `entailer!`, substitute `a`, `b`, and `c`, call the helper lemma, and finish arithmetic with `lia`. The return witnesses need `subst n_pre` before reducing `tribonacci_z n_pre`.
