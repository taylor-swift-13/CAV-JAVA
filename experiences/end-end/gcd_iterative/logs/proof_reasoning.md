## 2026-04-22 manual obligations after successful symexec

Fresh `symexec` succeeded on `annotated/verify_20260422_170350_gcd_iterative.c` and generated three manual placeholders in `coq/generated/gcd_iterative_proof_manual.v`:

```coq
Lemma proof_of_gcd_iterative_entail_wit_1 : gcd_iterative_entail_wit_1.
Proof. Admitted.

Lemma proof_of_gcd_iterative_entail_wit_2 : gcd_iterative_entail_wit_2.
Proof. Admitted.

Lemma proof_of_gcd_iterative_return_wit_1 : gcd_iterative_return_wit_1.
Proof. Admitted.
```

The exact generated witness shapes in `gcd_iterative_goal.v` are:

```coq
Definition gcd_iterative_entail_wit_1 :=
forall (b_pre: Z) (a_pre: Z), ... |--
  EX (g: Z), ... gcd_iterative_spec a_pre b_pre g ...

Definition gcd_iterative_entail_wit_2 :=
forall (b_pre: Z) (a_pre: Z) (g_2: Z) (b: Z) (a: Z),
  [| b <> 0 |] && ... [| gcd_iterative_spec a b g_2 |] ...
|--
  EX (g: Z), ... [| gcd_iterative_spec b (a % b) g |] ...

Definition gcd_iterative_return_wit_1 :=
forall (b_pre: Z) (a_pre: Z) (g: Z) (b: Z) (a: Z),
  [| b = 0 |] && ... [| gcd_iterative_spec a b g |] ...
|--
  [| gcd_iterative_spec a_pre b_pre a |] && emp.
```

The first witness is invariant initialization: choose `g = Z.gcd a_pre b_pre`, unfold `gcd_iterative_spec`, and the two spec facts are reflexive.

The second witness is invariant preservation: choose the old witness `g_2`. The pure obligations are nonnegativity of `a mod b`, positivity of `b + a mod b`, and the gcd preservation fact. Since the loop branch gives `b <> 0` and the invariant has `0 <= b`, we get `0 < b`; `Z.mod_pos_bound` gives `0 <= a mod b`, and Euclid preservation follows from `Z.gcd_mod` plus commutativity of `Z.gcd`.

The return witness uses the exit fact `b = 0`, `0 <= a`, and `gcd_iterative_spec a b g`. After unfolding the spec, `Z.gcd_0_r_nonneg` rewrites `Z.gcd a 0` to `a`, so the shared witness `g` is equal to the returned value.

## 2026-04-22 first compile failure in gcd helper

The first full compile replay reached `gcd_iterative_proof_manual.v` and failed at the local helper lemma:

```text
File ".../gcd_iterative_proof_manual.v", line 32, characters 2-31:
Error: Found no subterm matching "Zgcd (?M3000 mod ?M3001) ?M3001"
in the current goal.
```

The failing tactic sequence was:

```coq
rewrite Z.gcd_comm.
rewrite Z.gcd_mod by exact Hb.
apply Z.gcd_comm.
```

The issue is that the unqualified commutativity rewrite can rewrite more than the intended left-hand gcd, leaving no subterm of the exact shape required by `Z.gcd_mod`. The next edit will pin the first rewrite to `Z.gcd_comm b (a mod b)`, then apply `Z.gcd_mod a b Hb` to the resulting left side and finish with `Z.gcd_comm b a`.

## 2026-04-22 second compile failure in preservation witness

After fixing the gcd helper, the next compile reached `proof_of_gcd_iterative_entail_wit_2` and failed at the first bullet after `entailer!`:

```text
Unable to unify "0 <= ?M8005 mod ?M8006 < ?M8006" with
"forall m : model, (&( "r") # Int |-> (a % b)) m -> (&( "r") # Int |->_) m".
```

The current script assumed the first remaining subgoal was the modulo nonnegativity fact:

```coq
entailer!; try lia.
- apply Z.mod_pos_bound; lia.
- apply gcd_iterative_step; assumption.
```

The proof state shows the first remaining goal is actually the separation frame that turns `r # Int |-> (a % b)` into `r # Int |->_`. The next edit will handle that frame first with `sep_apply store_int_undef_store_int; entailer!`, then leave the modulo and gcd facts as later bullets.

## 2026-04-22 third compile failure in preservation witness

The next compile showed that `entailer!` plus `lia` already discharged the modulo nonnegativity and positivity obligations. After the separation frame, the remaining goal was:

```text
g_2 = Zgcd b (a % b)
```

but the script still tried to apply `Z.mod_pos_bound`, producing:

```text
Unable to unify "0 <= ?M8007 mod ?M8008 < ?M8008" with
"g_2 = Zgcd b (a % b)".
```

The next edit removes the stale modulo bullet and applies `gcd_iterative_step` directly to this remaining gcd-preservation goal.

## 2026-04-22 fourth compile failure: wrapped helper did not match unfolded equality

The next compile still stopped in `proof_of_gcd_iterative_entail_wit_2`:

```text
Unable to unify "?M8009 = Zgcd ?M8008 (?M8007 mod ?M8008)" with
"g_2 = Zgcd b (a % b)".
```

The remaining goal is already the unfolded equality form of `gcd_iterative_spec b (a % b) g_2`, while `gcd_iterative_step` concludes the wrapped predicate. Coq did not unfold the wrapper during `apply`. The next edit will prove the equality inline: unfold `gcd_iterative_spec` in `H4`, substitute `g_2`, rewrite the left side with `Z.gcd_comm b (a mod b)`, apply `Z.gcd_mod a b H`, and finish with `Z.gcd_comm`.

## 2026-04-22 coqtop proof-state check for preservation witness

Running the theorem interactively showed the precise post-`entailer!` subgoal order:

```text
goal 1: &( "r") # Int |-> (a % b) |-- &( "r") # Int |->_
goal 2: gcd_iterative_spec b (a % b) g_2
goal 3: 0 < b + a % b
goal 4: 0 <= a % b
```

After unfolding `H4 : gcd_iterative_spec a b g_2` and substituting `g_2`, goal 2 remains wrapped:

```text
gcd_iterative_spec b (a % b) (Zgcd a b)
```

So the stable proof is to use the local `gcd_iterative_step` helper on the wrapped goal, with the old current-pair spec proved by unfolding to reflexivity. Goals 3 and 4 are discharged from `b <> 0`, `0 <= b`, and `Z.mod_pos_bound`.

## 2026-04-22 C remainder notation is `Z.rem`

A focused notation check with `Set Printing All` showed that the generated expression `a % ( b )` under `Local Open Scope sac` is `Z.rem a b`, not `Z.modulo a b`:

```coq
fun a b : Z => Z.rem a b
```

This explains why rewrites using `Z.gcd_mod` and `Z.mod_pos_bound` did not match the generated goals. The correct preservation proof uses `Z.gcd_rem` for the Euclidean gcd step. The remainder range facts first rewrite with:

```coq
Z.rem_mod_nonneg a b : 0 <= a -> 0 < b -> Z.rem a b = a mod b
```

and only then use `Z.mod_pos_bound` on the nonnegative modulo form.

The first helper edit still wrote its conclusion with Coq's `mod` keyword:

```coq
gcd_iterative_spec b (a mod b) g
```

That parsed as `Z.modulo`, not the generated `Z.rem`, and compile failed with:

```text
Unable to unify "a mod b" with "a % b".
```

The helper conclusion must use the generated C remainder notation:

```coq
gcd_iterative_spec b (a % ( b )) g
```

## 2026-04-22 return witness needed explicit exit substitution

After the remainder/gcd fixes, compilation reached `proof_of_gcd_iterative_return_wit_1` and failed inside:

```coq
eapply gcd_iterative_zero_right; eauto; lia.
```

with:

```text
Tactic failure: Cannot find witness.
```

The return witness context contains the loop-exit equality `H : b = 0` and the current-pair spec `H4 : gcd_iterative_spec a b g`. The helper expects exactly `gcd_iterative_spec a 0 g`, so the proof should first `subst b`, then call:

```coq
eapply gcd_iterative_zero_right; [lia | exact H4].
```
