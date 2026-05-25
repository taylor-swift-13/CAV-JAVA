## 2026-04-22 Manual proof round 1

Fresh `symexec` on the current annotated file succeeded and generated `coq/generated/fibonacci_proof_manual.v` with four admitted obligations:

```coq
Lemma proof_of_fibonacci_safety_wit_6 : fibonacci_safety_wit_6.
Proof. Admitted.

Lemma proof_of_fibonacci_entail_wit_1 : fibonacci_entail_wit_1.
Proof. Admitted.

Lemma proof_of_fibonacci_entail_wit_2 : fibonacci_entail_wit_2.
Proof. Admitted.

Lemma proof_of_fibonacci_return_wit_1 : fibonacci_return_wit_1.
Proof. Admitted.
```

The relevant generated goals are all pure scalar obligations after the separation-logic framing is discharged:

```coq
Definition fibonacci_safety_wit_6 :=
forall (n_pre: Z) (b: Z) (a: Z) (i: Z),
  ... [| (i <= n_pre) |] ... [| (n_pre <= 46) |]
  ... [| (a = fib_z (i - 2)) |] ... [| (b = fib_z (i - 1)) |]
|-- [| (a + b <= INT_MAX) |] && [| (INT_MIN <= a + b) |].

Definition fibonacci_entail_wit_2 :=
forall (n_pre: Z) (b: Z) (a: Z) (i: Z),
  ... [| (a = fib_z (i - 2)) |] ... [| (b = fib_z (i - 1)) |]
|-- ... [| (b = fib_z ((i + 1) - 2)) |]
    && [| (a + b = fib_z ((i + 1) - 1)) |] ...
```

These obligations are analogous to the already verified scalar DP example `climb_stairs`: the loop index is bounded by a small contract constant, and the imported Fibonacci function computes by `Z.to_nat`, so concrete index cases reduce by `vm_compute`. The first proof attempt will add local tactics:

```coq
Ltac zcase x n :=
  let Heq := fresh "Heq" in
  let Hneq := fresh "Hneq" in
  destruct (Z.eq_dec x n) as [Heq | Hneq];
  [ subst; vm_compute; repeat split; try congruence; lia | idtac ].

Ltac split_small_range x :=
  zcase x 0; ...; zcase x 46; lia.
```

Planned proof shape:

- `safety_wit_6`: `pre_process; entailer!; subst a; subst b; split_small_range i.` This proves the int range for `fib_z(i-2) + fib_z(i-1)` by enumerating the only possible loop indices.
- `entail_wit_1`: `pre_process` should solve initialization; the concrete facts are `fib_z 0 = 0`, `fib_z 1 = 1`, and arithmetic from `n_pre <> 0`, `0 <= n_pre`.
- `entail_wit_2`: `pre_process; entailer!; subst a; subst b; split_small_range i.` This proves the recurrence preservation by concrete evaluation for bounded `i`.
- `return_wit_1`: `pre_process; entailer!; vm_compute; lia.` This proves `0 = fib_z 0` after the `n_pre = 0` branch condition.

No new axiom is needed. The helper tactics are local proof automation only, copied in shape from the prior scalar recurrence proof and adjusted to include index 46.

## 2026-04-22 Manual proof round 2

The first proof script used `split_small_range i` directly inside `entailer!` for both `safety_wit_6` and `entail_wit_2`. During the full compile, `original/fibonacci.v`, `fibonacci_goal.v`, and `fibonacci_proof_auto.v` compiled, but `coqc` then spent over 40 seconds in `fibonacci_proof_manual.v` without reaching the next log line. The compile log at interruption was:

```text
compile_start=2026-04-22T16:36:19+08:00
compiled=original/fibonacci.v
compiled=fibonacci_goal.v
compiled=fibonacci_proof_auto.v
```

This points to the repeated `vm_compute` calls being too expensive when run inside the main separation-logic proof context. The next edit will move bounded Fibonacci arithmetic into two small pure helper lemmas:

```coq
Lemma fib_z_sum_int_bound_2_46 :
  forall i, 2 <= i -> i <= 46 ->
    INT_MIN <= fib_z (i - 2) + fib_z (i - 1) <= INT_MAX.

Lemma fib_z_step_2_46 :
  forall i, 2 <= i -> i <= 46 ->
    fib_z (i - 2) + fib_z (i - 1) = fib_z i.
```

The helper lemmas still use bounded concrete evaluation, but they run in pure arithmetic goals only. The witness proofs should then reduce to `pre_process`, `entailer!`, `subst`, and calls to the helpers with bounds discharged by `lia`.

After isolating `fibonacci_entail_wit_2` in `coqtop`, `entailer!; subst a; subst b` leaves three subgoals in this order, not two:

```coq
1. &( "c") # Int |-> (fib_z (i - 2) + fib_z (i - 1)) |-- &( "c") # Int |-_
2. fib_z (i - 2) + fib_z (i - 1) = fib_z (i + 1 - 1)
3. fib_z (i - 1) = fib_z (i + 1 - 2)
```

The first goal is the separation-logic weakening from a concrete `Int` cell to an unknown `Int` cell and should be solved by `entailer!`. The previous script mistakenly treated the first bullet as the arithmetic equality, so Coq reported `Proof is not complete` at `reflexivity`. The corrected proof handles the heap weakening first, then the recurrence equality, then the arithmetic index normalization equality.

`entailer!` alone does not rewrite a concrete scalar store into an undefined scalar store. Testing the first subgoal in `coqtop` showed that `sep_apply store_int_undef_store_int` from `SimpleC.SL.StoreAux` changes:

```coq
&( "c") # Int |-> (fib_z (i - 2) + fib_z (i - 1)) |-- &( "c") # Int |-_
```

into the reflexive undefined-store entailment:

```coq
&( "c") # Int |-_ |-- &( "c") # Int |-_
```

and then `entailer!` finishes that subgoal. The proof file therefore needs `From SimpleC.SL Require Import ... StoreAux.` and the first `entail_wit_2` bullet should be:

```coq
- sep_apply store_int_undef_store_int.
  entailer!.
```

The next isolated failure was `fibonacci_return_wit_1`: after `pre_process; entailer!`, the remaining pure goal is:

```coq
n_pre : Z
H : n_pre = 0
...
============================
0 = fib_z n_pre
```

Running `vm_compute` before substituting `n_pre` does not reduce `fib_z n_pre`, so `lia` reports `Cannot find witness`. The stable proof is to `subst n_pre` first, then `vm_compute; lia`.
