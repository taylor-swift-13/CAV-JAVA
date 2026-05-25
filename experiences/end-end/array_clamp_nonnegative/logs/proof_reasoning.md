## 2026-04-22 02:38:00 +0800 - Manual entailment witnesses after successful symexec

Fresh symbolic execution succeeded and generated:

```text
coq/generated/array_clamp_nonnegative_goal.v
coq/generated/array_clamp_nonnegative_proof_auto.v
coq/generated/array_clamp_nonnegative_proof_manual.v
coq/generated/array_clamp_nonnegative_goal_check.v
```

`array_clamp_nonnegative_proof_manual.v` contains three admitted manual lemmas:

```coq
Lemma proof_of_array_clamp_nonnegative_entail_wit_2_1 : array_clamp_nonnegative_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_clamp_nonnegative_entail_wit_2_2 : array_clamp_nonnegative_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_clamp_nonnegative_entail_wit_3 : array_clamp_nonnegative_entail_wit_3.
Proof. Admitted.
```

The first two witnesses are loop-preservation entailments. The true branch has heap `IntArray.full a_pre n_pre (replace_Znth i 0 lc_2)` and must re-establish the invariant at `i + 1`. The correct existential witness is `replace_Znth i 0 lc_2`. For indices `k < i`, the old prefix facts continue to apply because replacing index `i` leaves other positions unchanged. For `k = i`, the write gives the negative case value `0`; the nonnegative case is contradictory because the old suffix fact gives `Znth i lc_2 0 = Znth i l 0` while the branch condition says `Znth i lc_2 0 < 0`.

The false branch keeps heap `IntArray.full a_pre n_pre lc_2`, so the witness is simply `lc_2`. For `k < i`, reuse the old prefix facts. For `k = i`, the old suffix fact links `lc_2[i]` to `l[i]`, and the branch condition `Znth i lc_2 0 >= 0` proves the nonnegative case while making the negative case contradictory.

The exit witness has assumptions `i >= n_pre` and `i <= n_pre`, so `i = n_pre`. Choosing `lc_2` directly gives the post-loop assertion; every index in `[0,n_pre)` is in the processed prefix. The proof should only need `Exists`, `entailer!`, a small `assert (i = n_pre) by lia`, and applying the two prefix implications.

The true-branch proof also needs stable local helpers:

```coq
Zlength (replace_Znth i x l) = Zlength l
Znth i (replace_Znth i x l) d = x
k <> i -> Znth k (replace_Znth i x l) d = Znth k l d
```

These are pure list facts about the repository's `replace_Znth` definition and will be added locally before the generated lemmas.

## 2026-04-22 02:43:55 +0800 - Proof compile repairs and final state

First compile attempt of `coq/generated/array_clamp_nonnegative_proof_manual.v` failed before any witness proof because Coq 8.20 parsed the helper proof line

```coq
induction l as [| h t IH]; intros n; destruct n; simpl; auto.
```

under the local scopes with:

```text
Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

I changed the helper proofs to use the simpler local naming form:

```coq
induction l; intros n; destruct n; simpl; auto.
```

The next proof issue was in `Znth_replace_Znth_diff`. The original statement only assumed `0 <= k < Zlength l` and `k <> i`, but after unfolding `Znth` / `replace_Znth`, Coq needed `Z.to_nat k <> Z.to_nat i`. This is not derivable from `k <> i` unless `i` is known nonnegative. I strengthened the helper with an explicit `0 <= i` premise:

```coq
Lemma Znth_replace_Znth_diff :
  forall {A : Type} (k i : Z) (x d : A) (l : list A),
    0 <= k < Zlength l ->
    0 <= i ->
    k <> i ->
    Znth k (replace_Znth i x l) d = Znth k l d.
```

After the helpers compiled, `entailer!` exposed the true-branch subgoals in reverse semantic order from the source assertion:

```text
goal 1: untouched suffix for k >= i + 1
goal 2: nonnegative prefix relation for k < i + 1
goal 3: negative prefix relation for k < i + 1
goal 4: Zlength (replace_Znth i 0 lc_2) = n_pre
```

I reordered `proof_of_array_clamp_nonnegative_entail_wit_2_1` accordingly. The false-branch witness similarly exposed:

```text
goal 1: untouched suffix
goal 2: nonnegative prefix relation
goal 3: negative prefix relation
```

I reordered `proof_of_array_clamp_nonnegative_entail_wit_2_2` to match that proof state. For `proof_of_array_clamp_nonnegative_entail_wit_3`, after asserting `i = n_pre`, choosing `lc_2`, and calling `entailer!`, all obligations were solved automatically; the earlier explicit bullets caused `Wrong bullet -: No more goals`, so they were removed.

Final proof state: `coqc` compiles `array_clamp_nonnegative_proof_manual.v`; `goal_check.v` compiles in the full documented sequence; `array_clamp_nonnegative_proof_manual.v` contains no `Admitted.` and no locally added `Axiom`.
