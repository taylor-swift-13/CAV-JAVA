## 2026-04-22 manual LCM proof plan

Current generated manual file:

```coq
Lemma proof_of_lcm_simple_safety_wit_3 : lcm_simple_safety_wit_3.
Proof. Admitted.

Lemma proof_of_lcm_simple_entail_wit_1 : lcm_simple_entail_wit_1.
Proof. Admitted.

Lemma proof_of_lcm_simple_entail_wit_2 : lcm_simple_entail_wit_2.
Proof. Admitted.

Lemma proof_of_lcm_simple_return_wit_1 : lcm_simple_return_wit_1.
Proof. Admitted.
```

The generated goals in `coq/generated/lcm_simple_goal.v` are pure scalar arithmetic and number-theory obligations. `lcm_simple_entail_wit_1` initializes the invariant after `x = a` and can choose `k = 1`; it needs the standard fact that positive `a` is at most `Z.lcm a b`. `lcm_simple_entail_wit_2` preserves the invariant after `x = x + a`; it needs to choose `k + 1` and prove `x + a <= Z.lcm a b` from `x = a * k`, `x <= Z.lcm a b`, and the branch fact `x mod b <> 0`. `lcm_simple_safety_wit_3` uses the same `x + a <= Z.lcm a b` fact plus the contract guard `Z.lcm a b <= INT_MAX` to discharge the C signed-int bound. `lcm_simple_return_wit_1` uses the exit fact `x mod b = 0`, the invariant multiple fact `x = a * k`, and `x <= Z.lcm a b` to prove `lcm_simple_spec a b x`, which unfolds to `x = Z.lcm a b`.

I will add local helper lemmas:

```coq
lcm_simple_value_pos :
  forall a b, 1 <= a -> 1 <= b -> 0 < lcm_simple_value a b

lcm_simple_value_ge_left :
  forall a b, 1 <= a -> 1 <= b -> a <= lcm_simple_value a b

lcm_simple_next_le_lcm :
  forall a b x k,
    x mod b <> 0 -> 1 <= a -> 1 <= b ->
    x = a * k -> x <= lcm_simple_value a b -> 1 <= k ->
    x + a <= lcm_simple_value a b

lcm_simple_exit_eq :
  forall a b x k,
    x mod b = 0 -> 1 <= a -> 1 <= b -> 1 <= k ->
    x = a * k -> x <= lcm_simple_value a b ->
    x = lcm_simple_value a b
```

The helper proof uses `Z.divide_lcm_l`, `Z.divide_lcm_r`, `Z.lcm_least`, `Z.mod_divide`, and `Z.divide_pos_le`. This is proof-stage work, not an annotation problem: the generated VC already contains the needed loop facts and branch/exit facts, and the remaining missing step is pure LCM arithmetic.

## 2026-04-22 first compile failure in positivity helper

Compile command:

```bash
coqc ... lcm_simple_proof_manual.v
```

Stable error:

```text
File ".../lcm_simple_proof_manual.v", line 34, characters 15-18:
Error: Tactic failure: Cannot find witness.
```

The failing code was:

```coq
pose proof (Z.divide_pos_le a (Z.lcm a b)) as Hle.
assert (a <= Z.lcm a b).
{ apply Hle; lia. }
```

This was circular: `Z.divide_pos_le a (Z.lcm a b)` requires `0 < Z.lcm a b`, which was exactly the fact the helper was trying to prove. The fix is to prove positivity by contradiction using `Z.lcm_nonneg` and `Z.lcm_eq_0`; with positive `a` and `b`, `Z.lcm a b = 0` is impossible, so nonnegativity strengthens to positivity. After that, `lcm_simple_value_ge_left` can safely use `Z.divide_pos_le`.

## 2026-04-22 safety witness bound mismatch

After fixing LCM positivity, `coqc` next failed in `proof_of_lcm_simple_safety_wit_3`:

```text
File ".../lcm_simple_proof_manual.v", line 109, characters 10-46:
Unable to unify "... <= lcm_simple_value ..." with "(x + a_pre ?= 2147483647) = Gt".
```

The first post-`entailer!` subgoal was the C upper-bound side condition `x + a_pre <= INT_MAX`, not the intermediate helper conclusion `x + a_pre <= lcm_simple_value a_pre b_pre`. The context already contains `lcm_simple_value a_pre b_pre <= INT_MAX`; therefore the proof should first pose `lcm_simple_next_le_lcm ...` and then close the actual bound with `lia`. I changed both safety subgoals to use that pattern rather than applying the helper directly to the wrong target shape.

The first rewrite of that pattern used `ltac:(auto)` arguments inside `pose proof`, and Coq could not infer the first premise `x mod b_pre <> 0` even though the context had it as hypothesis `H`. To avoid brittle generated names and explicit proof-term holes, I changed the bullets to:

```coq
assert (Hnext : x + a_pre <= lcm_simple_value a_pre b_pre).
{ eapply lcm_simple_next_le_lcm; eauto; lia. }
lia.
```

This lets `eauto` pick up the branch and equality facts from the current VC context, while `lia` handles repeated lower-bound hypotheses and the final `INT_MAX` comparison.

The next compile error showed a notation mismatch:

```text
The term "H" has type "x % b_pre <> 0" while it is expected to have type
"x mod b_pre <> 0"
```

The generated VC prints the C `%` expression as Coq `Z.rem` notation (`x % b_pre`), while the helper lemmas had been written with `x mod b`. Those are not definitionally the same in Coq. I changed the helper premises to use `x % b` and changed the divisibility conversions from `Z.mod_divide` to `Z.rem_divide`, matching the generated VC shape exactly.
