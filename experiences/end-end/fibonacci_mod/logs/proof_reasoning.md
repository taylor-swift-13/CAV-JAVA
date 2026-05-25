## 2026-04-22 Proof round 1

Current generated proof file: `output/verify_20260422_164639_fibonacci_mod/coq/generated/fibonacci_mod_proof_manual.v`. It contains three admitted manual obligations:

```coq
Lemma proof_of_fibonacci_mod_entail_wit_1 : fibonacci_mod_entail_wit_1.
Proof. Admitted.

Lemma proof_of_fibonacci_mod_entail_wit_2 : fibonacci_mod_entail_wit_2.
Proof. Admitted.

Lemma proof_of_fibonacci_mod_return_wit_1 : fibonacci_mod_return_wit_1.
Proof. Admitted.
```

The corresponding goals in `fibonacci_mod_goal.v` are pure obligations generated from loop invariant initialization, loop invariant preservation, and the early return branch `n == 0`. `entail_wit_1` must prove the invariant at the first loop control point: `0 = fib_mod_z (2 - 2) mod_pre`, `1 % mod_pre = fib_mod_z (2 - 1) mod_pre`, and the positive-mod remainder bounds for `1 % mod_pre`. `entail_wit_2` must prove the next loop invariant after executing `c = (a + b) % mod; a = b; b = c; ++i`, especially `((a + b) % mod_pre) = fib_mod_z ((i + 1) - 1) mod_pre` and the range bound for that remainder. `return_wit_1` must prove the early return value `0 = fib_mod_z n_pre mod_pre` under `n_pre = 0`.

The existing script `Proof. Admitted.` is insufficient because these facts require unfolding the task-specific Coq definition in `original/fibonacci_mod.v` and using `Z.rem` bounds for positive modulus. Planned helper lemmas:

```coq
Lemma fib_mod_z_0 : forall m, fib_mod_z 0 m = 0.
Lemma fib_mod_z_1 : forall m, fib_mod_z 1 m = Z.rem 1 m.
Lemma fib_mod_nat_step : forall n m,
  fib_mod_nat (S (S n)) m = Z.rem (fib_mod_nat n m + fib_mod_nat (S n) m) m.
Lemma fib_mod_z_step : forall i m,
  2 <= i -> fib_mod_z i m = Z.rem (fib_mod_z (i - 2) m + fib_mod_z (i - 1) m) m.
Lemma Z_rem_pos_bound : forall x m, 0 < m -> 0 <= Z.rem x m < m.
```

The main witnesses should then stay short: run `pre_process`, use `entailer!`, rewrite base/step lemmas, and use `lia` for scalar bounds. If compilation fails, the next step is to inspect the exact remaining subgoal with `coqtop` or a targeted `coqc` run and append a second proof reasoning section before changing the proof again.

## 2026-04-22 Proof round 2

The first compile failed in the helper lemma `fib_mod_z_step`, before reaching any witness proof:

```text
File ".../fibonacci_mod_proof_manual.v", line 66, characters 4-32:
Error: Found no subterm matching "Z.to_nat (?M3177 + ?M3178)" in the current goal.
```

The failing proof fragment was:

```coq
replace i with ((i - 2) + 2) at 1 by lia.
rewrite Z2Nat.inj_add by lia.
simpl.
reflexivity.
```

This was too brittle because after the earlier `replace (Z.to_nat i) with ...`, the second generated subgoal is an equality between naturals, and the expected `Z.to_nat ((i - 2) + 2)` syntactic shape is not guaranteed at that point. The repair is to avoid rewriting under a guessed syntactic occurrence and instead prove the natural equality by converting both sides through `Z.of_nat` using `Nat2Z.inj`; with nonnegative bounds, `Z2Nat.id` and `Nat2Z.inj_succ` reduce the goal to arithmetic.

Planned change: replace the second branch of `fib_mod_z_step` with a `Nat2Z.inj` proof:

```coq
apply Nat2Z.inj.
rewrite Z2Nat.id by lia.
rewrite Nat2Z.inj_succ, Nat2Z.inj_succ.
rewrite Z2Nat.id by lia.
lia.
```

This keeps the recurrence helper general and does not require changing the C annotation or rerunning symexec.

## 2026-04-22 Proof round 3

After fixing `fib_mod_z_step`, the next compile failed in `proof_of_fibonacci_mod_entail_wit_1`:

```text
File ".../fibonacci_mod_proof_manual.v", line 86, characters 4-23:
Error: Found no subterm matching "fib_mod_z 0 ?M39747" in the current goal.
```

A targeted `coqtop` run showed that after `pre_process; entailer!.`, the base-case equalities are already solved automatically. The only remaining subgoals are the two remainder bounds:

```coq
1 % mod_pre < mod_pre
0 <= 1 % mod_pre
```

The earlier script had four bullets and tried to rewrite base equalities that were no longer present. Planned change: make `proof_of_fibonacci_mod_entail_wit_1` use only the two actual subgoals after `entailer!`, both discharged by `Z_rem_nonneg_bound 1 mod_pre` and `lia`.

## 2026-04-22 Proof round 4

A targeted `coqtop` run for `fibonacci_mod_entail_wit_2` showed that `pre_process; entailer!; subst a; subst b` leaves five subgoals, in this exact order:

```coq
&( "c") # Int |-> ((fib_mod_z (i - 2) mod_pre + fib_mod_z (i - 1) mod_pre) % mod_pre) |-- &( "c") # Int |->_
(fib_mod_z (i - 2) mod_pre + fib_mod_z (i - 1) mod_pre) % mod_pre < mod_pre
0 <= (fib_mod_z (i - 2) mod_pre + fib_mod_z (i - 1) mod_pre) % mod_pre
(fib_mod_z (i - 2) mod_pre + fib_mod_z (i - 1) mod_pre) % mod_pre = fib_mod_z (i + 1 - 1) mod_pre
fib_mod_z (i - 1) mod_pre = fib_mod_z (i + 1 - 2) mod_pre
```

The previous script assumed the two semantic equalities came before the remainder bounds, causing Coq to try `reflexivity` on the upper-bound goal. The repair is only bullet reordering: first convert the `c` store to undef, then prove upper and lower remainder bounds with `Z_rem_nonneg_bound`, then prove the recurrence equality with `fib_mod_z_step`, and finally prove the index-shift equality by replacing `(i + 1) - 2` with `i - 1`.

## 2026-04-22 Proof round 5

The next compile reached the recurrence equality in `proof_of_fibonacci_mod_entail_wit_2` and failed at:

```coq
replace ((i + 1) - 1) with i by lia.
rewrite fib_mod_z_step by lia.
```

with:

```text
Error: Tactic failure: Cannot find witness.
```

This is not a failed mathematical side condition; it is Coq failing to infer the quantified arguments of `fib_mod_z_step` during a bare `rewrite`. The current goal has the RHS `fib_mod_z i mod_pre`, so the next change is to call the helper with explicit arguments:

```coq
rewrite (fib_mod_z_step i mod_pre) by lia.
```

That should rewrite `fib_mod_z i mod_pre` to the modulo recurrence while leaving only reflexivity.
