## 2026-04-22 15:01 CST - Manual entailment witnesses after successful symexec

The latest `symexec` run succeeded on `annotated/verify_20260422_145616_count_divisors.c`:

```text
symexec_start: 2026-04-22 15:00:26 +0800
symexec_end: 2026-04-22 15:00:26 +0800
symexec_exit: 0
symexec_elapsed_seconds: 0.10
```

It generated nonempty `count_divisors_goal.v`, `count_divisors_proof_auto.v`, `count_divisors_proof_manual.v`, and `count_divisors_goal_check.v`. The manual proof file has four admitted obligations:

```text
proof_of_count_divisors_entail_wit_1
proof_of_count_divisors_entail_wit_2_1
proof_of_count_divisors_entail_wit_2_2
proof_of_count_divisors_entail_wit_3
```

The relevant generated goals are:

```coq
Definition count_divisors_entail_wit_1 :=
forall (n_pre: Z),
  [| 1 <= n_pre |] && [| n_pre < INT_MAX |] && emp
|--
  ... [| 0 = count_divisors_upto_z n_pre (1 - 1) |] ... && emp.

Definition count_divisors_entail_wit_2_1 :=
forall (n_pre cnt d: Z),
  [| n_pre % d = 0 |] && [| d <= n_pre |] && ... &&
  [| cnt = count_divisors_upto_z n_pre (d - 1) |] && emp
|--
  ... [| cnt + 1 = count_divisors_upto_z n_pre ((d + 1) - 1) |] ... && emp.

Definition count_divisors_entail_wit_2_2 :=
forall (n_pre cnt d: Z),
  [| n_pre % d <> 0 |] && [| d <= n_pre |] && ... &&
  [| cnt = count_divisors_upto_z n_pre (d - 1) |] && emp
|--
  ... [| cnt = count_divisors_upto_z n_pre ((d + 1) - 1) |] ... && emp.

Definition count_divisors_entail_wit_3 :=
forall (n_pre cnt d: Z),
  [| d > n_pre |] && [| d <= n_pre + 1 |] &&
  [| cnt = count_divisors_upto_z n_pre (d - 1) |] && emp
|--
  [| d = n_pre + 1 |] && [| cnt = count_divisors_spec n_pre |] && emp.
```

The separation part is only `emp`, so `pre_process; entailer!` should leave pure arithmetic and definitional equalities. The first witness needs the helper fact `count_divisors_upto_z n 0 = 0`. The two preservation witnesses need one-step lemmas for the positive candidate `d`: if `n_pre % d = 0`, adding candidate `d` increases the helper by one; otherwise it is unchanged. The supplied Coq definition uses `Z.rem`, while generated C `%` premises use Coq's `%` notation, so the helper lemmas must bridge `Z.rem n d` and `n % d` under `d <> 0`. The exit witness needs `d = n_pre + 1` from `d > n_pre` and `d <= n_pre + 1`, then `count_divisors_spec_as_upto_z`.

I will add these local helper lemmas to `coq/generated/count_divisors_proof_manual.v` before the generated proof lemmas:

```coq
Lemma count_divisors_upto_z_zero : forall n, count_divisors_upto_z n 0 = 0.
Lemma count_divisors_upto_z_step_divides :
  forall n d, 1 <= d -> n % d = 0 ->
    count_divisors_upto_z n d = count_divisors_upto_z n (d - 1) + 1.
Lemma count_divisors_upto_z_step_not_divides :
  forall n d, 1 <= d -> n % d <> 0 ->
    count_divisors_upto_z n d = count_divisors_upto_z n (d - 1).
```

Then each witness proof should reduce to `pre_process; entailer!`, rewriting with the corresponding helper, and `lia` for remaining bounds.

## 2026-04-22 15:02 CST - Coq parser requires generated modulo notation shape

The first compile of `coq/generated/count_divisors_proof_manual.v` failed before proof checking the witnesses:

```text
File ".../count_divisors_proof_manual.v", line 35, characters 4-9:
Error: Unknown scope delimiting key d.
```

The failing helper statement used:

```coq
n % d = 0
```

In this generated proof environment, bare `n % d` is parsed as a scope-delimited notation attempt with key `d`. The generated goals themselves write the C remainder proposition with the right operand parenthesized:

```coq
[| ((n_pre % ( d ) ) = 0) |]
```

I will keep the same semantic helper shape but change the helper premises to `n % (d) = 0` and `n % (d) <> 0` so they parse like the generated VC hypotheses and can be used directly by `rewrite ... by lia`.

The next compile reached the helper proof and failed at the `Z.eq_dec` true branch:

```text
File ".../count_divisors_proof_manual.v", line 45, characters 4-7:
Error: Tactic failure: Cannot find witness.
```

At that branch, after unfolding `count_divisors_upto_z`, normalizing the positive fuel, and destructing `Z.eq_dec (Z.rem n d) 0`, the goal is already the same expression on both sides. This is not an arithmetic search problem; `reflexivity` is the stable proof. I will replace that branch's `lia` with `reflexivity`.

That exposed one more normalization detail. Coq simplified `Z.of_nat (S (Z.to_nat (d - 1)))` inside the recursive divisor test to:

```coq
Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1)))
```

so the helper proof still had:

```text
Unable to unify "count_divisors_upto n (Z.to_nat (d - 1)) + 1" with
"count_divisors_upto n (Z.to_nat (d - 1)) +
 (if Z.eq_dec (n % Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1)))) 0 then 1 else 0)".
```

The mathematical fact is still just `Z.of_nat (S (Z.to_nat (d - 1))) = d` for `1 <= d`; the proof needs to rewrite the normalized constructor term explicitly before destructing `Z.eq_dec`. I will add:

```coq
replace (Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1)))) with d by lia.
```

in both step helper lemmas after `simpl`.

The next compile showed that the earlier planned `Z.rem_mod` bridge is not needed in this generated environment:

```text
The term "Hmod" has type "n % d = 0" while it is expected to have type
"Z.sgn n * (Zabs n mod Zabs d) = 0".
```

Both the generated VC hypothesis and the `Z.eq_dec (Z.rem n d) 0` branch print as `n % d`, so the contradiction branches can use `Hmod` and `Hrem` directly. I will remove the `rewrite Z.rem_mod` / `rewrite <- Z.rem_mod` steps.

The next compile reached the false branch of `count_divisors_upto_z_step_not_divides` and left only an additive-zero normalization:

```text
Unable to unify "count_divisors_upto n (Z.to_nat (d - 1))" with
"count_divisors_upto n (Z.to_nat (d - 1)) + 0".
```

This is stable to close by rewriting `Z.add_0_r` before `reflexivity`.

The next compile showed `proof_of_count_divisors_entail_wit_1` is fully solved by `pre_process; entailer!.` once `count_divisors_upto_z_zero` is in scope:

```text
File ".../count_divisors_proof_manual.v", line 76, characters 2-12:
Error: No such goal.
```

The extra rewrite after `entailer!` was therefore stale; I will remove it and leave only the solved proof skeleton.

Recompiling showed the same `No such goal` now points at `entailer!` itself in `proof_of_count_divisors_entail_wit_1`; `pre_process` already closes this pure initialization entailment. I will reduce that proof to just:

```coq
Proof.
  pre_process.
Qed.
```

## 2026-04-22 15:09 CST - Reapply proof after regenerated strengthened invariant VCs

After strengthening the invariant with `cnt <= d - 1`, I reran `symexec` as required. The regenerated `count_divisors_entail_wit_2_1` now includes the needed premise and conclusion:

```coq
[| cnt <= d - 1 |]
...
[| cnt + 1 <= (d + 1) - 1 |]
[| cnt + 1 <= n_pre |]
```

The helper lemmas from the previous proof attempt remain the right proof structure. The witness scripts need only account for the regenerated file by reinserting the local lemmas and proving the branch witnesses with explicit arithmetic normalization:

```coq
replace (d + 1 - 1) with d by lia.
rewrite count_divisors_upto_z_step_divides by lia.
```

and similarly for the non-dividing branch. The exit witness will derive `d = n_pre + 1`, normalize `n_pre + 1 - 1` to `n_pre`, and rewrite `count_divisors_spec_as_upto_z`.
