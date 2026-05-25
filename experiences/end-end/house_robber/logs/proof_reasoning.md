## 2026-04-22 17:30 +0800 - Manual proof plan after fresh symexec

Fresh `symexec` succeeded on `annotated/verify_20260422_171952_house_robber.c` and generated five manual obligations in `coq/generated/house_robber_proof_manual.v`:

```coq
Lemma proof_of_house_robber_safety_wit_4 : house_robber_safety_wit_4.
Lemma proof_of_house_robber_entail_wit_1 : house_robber_entail_wit_1.
Lemma proof_of_house_robber_entail_wit_2_1 : house_robber_entail_wit_2_1.
Lemma proof_of_house_robber_entail_wit_2_2 : house_robber_entail_wit_2_2.
Lemma proof_of_house_robber_return_wit_1 : house_robber_return_wit_1.
```

The important generated goals are:

```coq
house_robber_safety_wit_4:
  ... i < n_pre ...
  prev1 = house_robber_spec (sublist 0 i l)
  (i = 0 -> prev2 = 0)
  (i > 0 -> prev2 = house_robber_spec (sublist 0 (i - 1) l))
  (i < n_pre -> prev2 + Znth i l 0 <= INT_MAX)
|-- prev2 + Znth i l 0 <= INT_MAX /\ INT_MIN <= prev2 + Znth i l 0

house_robber_entail_wit_2_1:
  branch prev2 + Znth i l 0 > prev1
|-- prev2 + Znth i l 0 =
    house_robber_spec (sublist 0 (i + 1) l)
    ... plus shifted prev2 and next-take overflow facts ...

house_robber_entail_wit_2_2:
  branch prev2 + Znth i l 0 <= prev1
|-- prev1 =
    house_robber_spec (sublist 0 (i + 1) l)
    ... plus shifted prev2 and next-take overflow facts ...

house_robber_return_wit_1:
  i_2 >= n_pre /\ i_2 <= n_pre /\
  prev1 = house_robber_spec (sublist 0 i_2 l) /\ Zlength l = n_pre
|-- prev1 = house_robber_spec l
```

The current proof state contains the right program facts; no annotation change is needed. The hard parts are pure list/DP facts for the Coq definition:

```coq
Fixpoint house_robber_acc prev2 prev1 l :=
  match l with
  | nil => prev1
  | x :: xs =>
      let take := prev2 + x in
      let cur := Z.max take prev1 in
      house_robber_acc prev1 cur xs
  end.

Definition house_robber_spec l := house_robber_acc 0 0 l.
```

Planned proof-only edit in `house_robber_proof_manual.v`:

- Add helper lemmas showing `house_robber_spec (sublist 0 (i + 1) l)` is `Z.max (prev2 + Znth i l 0) prev1` under the invariant's `prev1` and `prev2` facts. The proof should split `i = 0` versus `i > 0`; the `i = 0` case unfolds the singleton prefix, and the positive case rewrites `sublist 0 (i + 1) l` as `sublist 0 i l ++ [Znth i l 0]` and uses the accumulator semantics.
- Add a helper for the next-iteration overflow guard: when `i + 1 < n_pre`, the contract's prefix bound for `k = i + 2` implies the next `prev1 + Znth (i + 1) l 0` is at most `INT_MAX`.
- Add a return helper using `i_2 = n_pre` and `Zlength l = n_pre` to rewrite `sublist 0 i_2 l` to `l`.

The witnesses themselves should use `pre_process; entailer!`, substitute the scalar equalities, and call these helpers. No `Axiom` or `Admitted.` may remain in `proof_manual.v`.

## 2026-04-22 17:37 +0800 - Proof iterations and final shape

The final `proof_manual.v` proof defines a local state function:

```coq
Fixpoint house_robber_state (prev2 prev1 : Z) (l : list Z) : Z * Z := ...
```

The key helper chain is:

```coq
house_robber_state_snd_acc
house_robber_state_app
house_robber_state_fst_snoc
house_robber_spec_snoc_state
house_robber_state_fst_prefix
house_robber_prefix_step
house_robber_next_take_bound
house_robber_full_sublist
```

This lets the generated witnesses avoid reproving list decomposition directly. `house_robber_prefix_step` rewrites:

```coq
house_robber_spec (sublist 0 (i + 1) l)
= Z.max (prev2 + Znth i l 0) prev1
```

under the loop invariant's facts for `prev1` and `prev2`. `house_robber_next_take_bound` derives the next iteration's overflow guard from the contract prefix bound at `k = i + 2`.

There were three proof-script issues during compilation:

- `Local Open Scope sac` was originally before the helper lemmas. This caused parse errors such as `Syntax error: [equality_intropattern] ... expected after 'as'` on `induction l as ...`, and singleton notation `[x]` was parsed as assertion syntax. I moved `Local Open Scope sac` below the helper lemmas and used conservative list syntax such as `x :: nil`.
- `entailer!` left witness bullets in an order different from the written script. For `entail_wit_2_1` and `entail_wit_2_2`, the actual order after the heap-weakening goal was the next-overflow implication, the shifted `prev2` implication, and only then the branch-specific prefix-step equality. I confirmed this with a temporary `Show.` probe and reordered the bullets.
- Two stack slots, `cur` and `take`, had to be weakened from concrete `Int |-> value` to undefined `Int |-_`. Each preservation witness therefore needs two applications of:

```coq
sep_apply store_int_undef_store_int.
sep_apply store_int_undef_store_int.
entailer!.
```

After these changes, `coq/generated/house_robber_proof_manual.v` compiles, contains no `Admitted.`, and contains no added `Axiom`.
