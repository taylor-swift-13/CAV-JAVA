# Proof reasoning

## 2026-04-22 05:29 - `array_is_strictly_increasing_return_wit_2`

The generated `proof_manual.v` contains exactly one placeholder:

```coq
Lemma proof_of_array_is_strictly_increasing_return_wit_2 : array_is_strictly_increasing_return_wit_2.
Proof. Admitted.
```

The corresponding goal in `array_is_strictly_increasing_goal.v` is the normal loop-exit return path:

```coq
Definition array_is_strictly_increasing_return_wit_2 :=
forall (a_pre: Z) (n_pre: Z) (l: list Z) (i_3: Z),
  [| i_3 >= n_pre |] &&
  [| 1 <= i_3 |] &&
  [| i_3 <= n_pre + 1 |] &&
  [| n_pre = Zlength l |] &&
  [| forall j, 1 <= j /\ j < i_3 ->
       Znth (j - 1) l 0 < Znth j l 0 |] &&
  [| 0 <= n_pre |] &&
  [| Zlength l = n_pre |] &&
  IntArray.full a_pre n_pre l
|--
  (EX i, [| 1 = 0 |] && ...) ||
  ([| 1 = 1 |] &&
   [| forall i_2, 1 <= i_2 /\ i_2 < n_pre ->
        Znth (i_2 - 1) l 0 < Znth i_2 l 0 |] &&
   IntArray.full a_pre n_pre l).
```

The left disjunct is impossible because it starts with `1 = 0`, so the proof must choose the right assertion-level disjunction with `Right`. After `pre_process`, `Intros`, and `entailer!`, the only nontrivial pure subgoal is the universal condition for every `i_2` below `n_pre`. The invariant already provides the same relation for every `j < i_3`; the loop-exit condition supplies `n_pre <= i_3`, so `i_2 < n_pre` implies `i_2 < i_3` by `lia`.

Planned proof:

```coq
Proof.
  pre_process.
  Intros.
  Right.
  entailer!.
  intros j [? ?].
  apply H3.
  lia.
Qed.
```

This follows the assertion-level disjunction guidance in `PROOF.md` item 22 and keeps the proof local to arithmetic plus the invariant's quantified hypothesis. If the generated hypothesis numbering differs after `Intros`, the compile step will identify the failing line and the next iteration will rename or locate the quantified hypothesis explicitly.
