## Manual proof iteration 1: obligations after regenerated symexec

Fresh `symexec` on `annotated/verify_20260422_154652_digit_sum.c` generated three manual obligations in `coq/generated/digit_sum_proof_manual.v`:

```coq
Lemma proof_of_digit_sum_safety_wit_3 : digit_sum_safety_wit_3.
Lemma proof_of_digit_sum_entail_wit_2 : digit_sum_entail_wit_2.
Lemma proof_of_digit_sum_return_wit_1 : digit_sum_return_wit_1.
```

`proof_of_digit_sum_safety_wit_3` is the C integer safety VC for `sum += n % 10`. Its context includes:

```coq
n > 0
0 <= n
0 <= sum
sum + n <= n_pre
sum + digit_sum_z n = digit_sum_z n_pre
0 <= n_pre
```

The needed bridge is the arithmetic lemma `0 <= n % 10 <= n` for positive `n`. Together with the invariant bound `sum + n <= n_pre` and the typed `Int` local state handled by `entailer!`, this should prove the upper and lower bounds for `sum + n % 10`.

`proof_of_digit_sum_entail_wit_2` preserves the loop invariant after:

```c
sum += n % 10;
n = n / 10;
```

The arithmetic pieces are `0 <= n / 10`, `0 <= sum + n % 10`, and `(sum + n % 10) + n / 10 <= n_pre`. The semantic piece is:

```coq
(sum + n % 10) + digit_sum_z (n / 10) = digit_sum_z n_pre
```

Using the old invariant equality, this reduces to a one-step unfolding lemma for positive inputs:

```coq
digit_sum_z n = Z.rem n 10 + digit_sum_z (n ÷ 10)
```

Because `input/digit_sum.v` defines `digit_sum_z` with explicit fuel `Z.to_nat n`, this one-step lemma needs helper lemmas showing that extra fuel beyond `Z.to_nat n` does not change `digit_sum_fuel`, plus a quotient-decrease fact `0 <= n ÷ 10 < n`.

`proof_of_digit_sum_return_wit_1` is the loop-exit VC. From `n <= 0` and `0 <= n`, we get `n = 0`; unfolding `digit_sum_z 0` gives `0`, and the invariant equality becomes `sum = digit_sum_z n_pre`.

I found an archived exact `digit_sum` proof after `CAV/examples` had no exact match. The reusable pattern is to introduce local lemmas `quot_10_lt_pos`, `rem_10_bounds_pos`, `digit_sum_fuel_stable`, `digit_sum_fuel_stable_ge`, and `digit_sum_z_step`, then keep the three witness proofs short with `pre_process`, `entailer!`, and `lia`.

## Manual proof iteration 2: fix fuel-stability subgoal ordering

The first compile replay failed in `digit_sum_fuel_stable` at the recursive call:

```coq
rewrite IHfuel; auto.
apply Nat2Z.inj_le.
```

The visible Coq error was:

```text
Unable to unify
 "((? <= ?)%nat -> Z.of_nat ? <= Z.of_nat ?) /\ ..."
with
 "(0 ?= n / 10) = Gt -> False".
```

This means the proof script tried to solve the recursive call's `0 <= n / 10` premise with the nat-order tactic intended for the later fuel-bound premise. The fix is to instantiate the induction hypothesis explicitly:

```coq
rewrite (IHfuel (n ÷ 10) extra).
```

and then discharge the generated premises in the intended order: reflexivity for the rewritten equality, `lia` using `quot_10_lt_pos` for nonnegativity, and a separate `Nat2Z.inj_le` block for `Z.to_nat (n ÷ 10) <= fuel`.

The compile replay also showed why the compile command must use `set -e`: without it, the shell continued to `goal_check.v` after `proof_manual.v` failed and produced a secondary missing-library error. The next compile run will stop on the first failed `coqc`.

## Manual proof iteration 3: align helper lemmas with `Z.div` in the current spec

The next fail-fast compile stopped at:

```text
Found no subterm matching "digit_sum_fuel (n ÷ 10) (fuel + extra)"
```

The archived proof used a previous `digit_sum.v` where the recursive call was `Z.quot n 10`. The current workspace's `output/verify_20260422_154652_digit_sum/original/digit_sum.v` instead defines:

```coq
else Z.rem n 10 + digit_sum_fuel (Z.div n 10) k
```

So the fuel-stability induction must recurse on `n / 10`, not `n ÷ 10`. The generated C goals still write the program division as `n ÷ 10`, so the proof needs both facts:

```coq
0 <= n / 10 < n
0 <= n ÷ 10 < n
```

and the bridge `Z.quot_div_nonneg` under `0 <= n` and `0 < 10`. I will add `div_10_lt_pos`, redefine `quot_10_lt_pos` through `Z.quot_div_nonneg`, use `n / 10` inside `digit_sum_fuel_stable`, and keep `digit_sum_z_step` returning the generated-goal shape with `digit_sum_z (n ÷ 10)`.

The first version of this bridge used:

```coq
replace (n / 10) with (n ÷ 10) by (symmetry; apply Z.quot_div_nonneg; lia).
```

but `Z.quot_div_nonneg` already has the orientation `n ÷ 10 = n / 10`, which is exactly what `replace (n / 10) with (n ÷ 10)` needs internally. The `symmetry` was backwards and caused Coq to try to unify the wrong equality direction. Removing `symmetry` should fix this local rewrite.

## Final proof status: blocked by missing input upper-bound contract

After adding the bridge assertion and preserving the `sum` local permission, `symexec` succeeded, but the generated manual proof file now contains:

```coq
Lemma proof_of_digit_sum_entail_wit_1 : digit_sum_entail_wit_1.
```

with the corresponding goal:

```coq
Definition digit_sum_entail_wit_1 :=
forall (n_pre: Z),
  [| (0 <= n_pre) |] && emp
|--
  [| (n_pre <= INT_MAX) |] &&
  [| (0 = 0) |] &&
  emp.
```

This obligation is false as a Coq proposition: from `0 <= n_pre` alone one cannot prove `n_pre <= 2147483647`. I also checked the imported integer automation on the distilled goal:

```coq
Goal forall n: Z, 0 <= n -> n <= INT_MAX.
```

and it remains unprovable because there is no range hypothesis for `n`. Earlier, without this explicit upper bound, the loop-body safety VC was also unprovable:

```coq
sum + n % 10 <= INT_MAX
```

from only `sum + n <= n_pre` and `0 <= n_pre`. Therefore the current Verify stage cannot complete without strengthening the formal input contract, for example by adding `n <= INT_MAX` to `input/digit_sum.c`'s `Require`. That change belongs to Contract, not Verify, so I am stopping with `Final Result: Fail` rather than editing the input contract or adding an unsound proof axiom.

## Retry proof status: equivalent entry witness after annotation repair attempt

This retry removed the explicit `n@pre <= INT_MAX` bridge assertion and regenerated Coq from the revised invariant that carries `sum + n <= INT_MAX`. The old witness:

```coq
[| (n_pre <= INT_MAX) |]
```

was not generated directly, but `digit_sum_entail_wit_1` now requires:

```coq
forall (n_pre: Z),
  [| (0 <= n_pre) |] && emp
|--
  [| ((0 + n_pre ) <= INT_MAX) |] && ...
```

This is propositionally the same missing fact. Because the left side is pure `0 <= n_pre` and `emp`, there is no local store or typed `Int` hypothesis for a manual proof to exploit. Starting a proof script for `proof_of_digit_sum_entail_wit_1` would reduce to the false arithmetic theorem:

```coq
forall n_pre : Z, 0 <= n_pre -> n_pre <= INT_MAX.
```

Therefore the retry does not edit `digit_sum_proof_manual.v`: replacing the generated `Admitted.` placeholders would require either changing the formal `Require` or adding an unsound axiom/admission, both outside the Verify-stage rules.

## Retry proof iteration: `by local` made the upper-bound witness sound

After adding the annotation:

```c
/*@ n <= INT_MAX by local */
```

before the loop and regenerating with `symexec`, the previous false pure entry witness changed. The current `coq/generated/digit_sum_goal.v` has:

```coq
Definition digit_sum_entail_wit_1 :=
forall (n_pre: Z),
  [| (0 <= n_pre) |]
  && ((( &( "sum" ) )) # Int |-> 0)
  ** ((( &( "n" ) )) # Int |-> n_pre)
|--
  [| (n_pre <= INT_MAX) |] &&
  ...
  ((( &( "n" ) )) # Int |-> n_pre)
  ** ((( &( "sum" ) )) # Int |-> 0).
```

This is no longer the false theorem `0 <= n_pre -> n_pre <= INT_MAX`; the left side still contains the `Int` local stores, so the generated auto proof can use local integer range information. The manual file is now reduced to three obligations:

```coq
Lemma proof_of_digit_sum_safety_wit_3 : digit_sum_safety_wit_3.
Lemma proof_of_digit_sum_entail_wit_3 : digit_sum_entail_wit_3.
Lemma proof_of_digit_sum_return_wit_1 : digit_sum_return_wit_1.
```

The archived proof at `./archieve/output_backup_20260422_011624/verify_20260421_022514_digit_sum/coq/generated/digit_sum_proof_manual.v` provides the right structure: local lemmas for quotient/rem bounds, a fuel-stability lemma, and a one-step unfolding lemma for `digit_sum_z`. The current input spec uses:

```coq
else Z.rem n 10 + digit_sum_fuel (Z.div n 10) k
```

while generated C goals use `n ÷ 10`, so the retry proof must adapt the archived proof by proving fuel stability over `Z.div n 10` and bridging to `Z.quot n 10` with `Z.quot_div_nonneg` under nonnegative operands.

Planned proof edit:

- Add helper lemmas `digit_sum_fuel_nonpositive`, `div_10_lt_pos`, `quot_10_lt_pos`, `rem_10_bounds_pos`, `digit_sum_fuel_stable`, `digit_sum_fuel_stable_ge`, and `digit_sum_z_step`.
- Prove `proof_of_digit_sum_safety_wit_3` using `rem_10_bounds_pos`, `sum + n <= n_pre`, and `n_pre <= INT_MAX`.
- Prove `proof_of_digit_sum_entail_wit_3` using `digit_sum_z_step`, `quot_10_lt_pos`, `rem_10_bounds_pos`, and `Z.quot_rem`.
- Prove `proof_of_digit_sum_return_wit_1` directly with `pre_process; entailer!`.

First fail-fast compile stopped in `coq/generated/digit_sum_proof_manual.v` at `quot_10_lt_pos`:

```text
File ".../digit_sum_proof_manual.v", line 48, characters 10-27:
Error: In environment
n : Z
Hn : 0 < n
Unable to unify "?M2998 ÷ ?M2999 = ?M2998 / ?M2999" with
"n / 10 = n ÷ 10".
```

The local script had:

```coq
replace (n ÷ 10) with (n / 10).
...
apply Z.quot_div_nonneg; lia.
```

For this `replace`, Coq asks for `n / 10 = n ÷ 10`, while `Z.quot_div_nonneg` provides `n ÷ 10 = n / 10`. The fix is to add `symmetry` in this lemma only. This is separate from the later `digit_sum_z_step` replacement, where the old term is `n / 10` and the new term is `n ÷ 10`.

The second compile confirmed that the later replacement is indeed the opposite case:

```text
File ".../digit_sum_proof_manual.v", line 137, characters 20-37:
Error:
In environment
n : Z
Hn : 0 < n
k : nat
Hk : Z.to_nat n = S k
Hleb : (n <=? 0) = false
Unable to unify "?M3060 ÷ ?M3061 = ?M3060 / ?M3061" with
"n / 10 = n ÷ 10".
```

At this line the script was:

```coq
replace (n / 10) with (n ÷ 10).
...
- symmetry. apply Z.quot_div_nonneg; lia.
```

For this replacement, the generated equality is already `n / 10 = n ÷ 10`; after `symmetry` it no longer matches. The fix is to remove `symmetry` in `digit_sum_z_step` while keeping it in `quot_10_lt_pos`.

The next compile reached `proof_of_digit_sum_entail_wit_3` and failed at the first bullet after `entailer!`:

```text
Unable to unify "(0 ?= ?M10493 ÷ ?M10494) = Gt -> False" with
"sum + n % 10 + digit_sum_z (n ÷ 10) = digit_sum_z n_pre".
```

This shows the first remaining subgoal is the semantic preservation equation, not the quotient nonnegativity side condition. The current hypotheses include:

```coq
H4 : sum + digit_sum_z n = digit_sum_z n_pre
```

The proof bullets should therefore start with:

```coq
rewrite <- H4.
rewrite (digit_sum_z_step n ltac:(lia)).
lia.
```

and only then handle the quotient/rem arithmetic side conditions.

After reordering `proof_of_digit_sum_entail_wit_3`, compile advanced to `proof_of_digit_sum_return_wit_1` and failed with:

```text
Error: (in proof proof_of_digit_sum_return_wit_1):
Attempt to save an incomplete proof (there are remaining open goals).
```

The return witness is:

```coq
forall (n_pre n sum: Z),
  [| n = 0 |] && [| sum = digit_sum_z n_pre |] && emp
|-- [| sum = digit_sum_z n_pre |] && emp.
```

So any remaining subgoal after `entailer!` is pure arithmetic/equality cleanup. I will add an explicit `lia` after `entailer!` rather than relying on `entailer!` to finish all pure goals.

Plain `lia` was still insufficient. A `coqtop` replay showed the actual post-`entailer!` state:

```coq
H : n <= 0
H0 : 0 <= n
H4 : sum + digit_sum_z n = digit_sum_z n_pre
============================
sum = digit_sum_z n_pre
```

So the proof must explicitly derive `n = 0`, rewrite the invariant equality, and unfold `digit_sum_z 0`:

```coq
assert (n = 0) by lia.
subst n.
replace (digit_sum_z 0) with 0 in H4 by (unfold digit_sum_z; reflexivity).
lia.
```
