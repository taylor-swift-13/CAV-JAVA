# Proof Reasoning

## Iteration 1: Manual witnesses after successful symexec

Fresh `symexec` succeeded on `annotated/verify_20260422_033321_array_count_transitions.c` and generated five manual obligations in `coq/generated/array_count_transitions_proof_manual.v`:

```coq
Lemma proof_of_array_count_transitions_safety_wit_5 : array_count_transitions_safety_wit_5.
Proof. Admitted.

Lemma proof_of_array_count_transitions_entail_wit_1 : array_count_transitions_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_count_transitions_entail_wit_2_1 : array_count_transitions_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_count_transitions_entail_wit_2_2 : array_count_transitions_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_count_transitions_return_wit_1 : array_count_transitions_return_wit_1.
Proof. Admitted.
```

The relevant generated goals are:

```coq
Definition array_count_transitions_safety_wit_5 := ...
  [| Znth i l 0 <> Znth (i - 1) l 0 |] &&
  [| i < n_pre |] &&
  [| cnt = array_count_transitions_spec (sublist 0 i l) |] &&
  [| n_pre <= INT_MAX |] &&
  [| Zlength l = n_pre |] |--
  [| cnt + 1 <= INT_MAX |] && [| INT_MIN <= cnt + 1 |].

Definition array_count_transitions_entail_wit_2_1 := ...
  [| Znth i l 0 <> Znth (i - 1) l 0 |] &&
  [| cnt = array_count_transitions_spec (sublist 0 i l) |] |--
  [| cnt + 1 =
     array_count_transitions_spec (sublist 0 (i + 1) l) |] && ...

Definition array_count_transitions_entail_wit_2_2 := ...
  [| Znth i l 0 = Znth (i - 1) l 0 |] &&
  [| cnt = array_count_transitions_spec (sublist 0 i l) |] |--
  [| cnt =
     array_count_transitions_spec (sublist 0 (i + 1) l) |] && ...

Definition array_count_transitions_return_wit_1 := ...
  [| i >= n_pre |] &&
  [| cnt = array_count_transitions_spec (sublist 0 i l) |] &&
  [| Zlength l = n_pre |] |--
  [| cnt = array_count_transitions_spec l |] && ...
```

The existing auto proof file already defines the other safety and partial-solve witnesses, so the manual file must not duplicate those names. The proof pattern should match the completed adjacent-count examples:

- Add a `sublist_prefix_full` helper so the return witness can rewrite `sublist 0 i l` to `l` from `Zlength l <= i`.
- Add a prefix-snoc helper for `sublist 0 (i + 1) l`.
- Add a `last_sublist_prefix_Z` helper to identify the previous element of the processed prefix as `Znth (i - 1) l 0`.
- Add a transition-spec snoc lemma, because unlike simple element counting, the contribution of a new element depends on the previous element.
- Add a bounds lemma stating that transition counts are nonnegative and at most the number of adjacent gaps in a nonempty list; this supplies the `cnt + 1` integer-range side condition.

Expected witness structure:

```coq
unfold array_count_transitions_entail_wit_2_1.
intros. entailer!. subst cnt.
rewrite array_count_transitions_spec_step by lia.
destruct (Z.eq_dec (Znth i l 0) (Znth (i - 1) l 0)); lia.
```

For `return_wit_1`, the key fact is that `i >= n_pre` and `Zlength l = n_pre`, so `sublist 0 i l = l` even in the `n == 0` skip-loop case where `i == 1`.

## Iteration 2: Fix bounds-helper nil case

The first compile replay stopped before any generated witness proof:

```text
File ".../array_count_transitions_proof_manual.v", line 160, characters 11-30:
Error: Found no subterm matching "Zlength nil" in the current goal.
```

The failing helper branch was:

```coq
Lemma array_count_transitions_spec_bounds :
  forall (l : list Z),
    0 <= array_count_transitions_spec l <= Z.max 0 (Zlength l - 1).
Proof.
  intros l.
  destruct l.
  - simpl. rewrite Zlength_nil. lia.
  ...
Qed.
```

After `simpl`, Coq has already simplified both `array_count_transitions_spec nil` and the `Zlength nil` expression enough that there is no literal `Zlength nil` subterm to rewrite. This is not a semantic issue; the nil case is pure arithmetic. Planned edit: replace that branch with `simpl. lia.` and rerun the full compile chain.

## Iteration 3: Make initialization prefix singleton explicit

The second compile replay reached `proof_of_array_count_transitions_entail_wit_1` and failed with:

```text
File ".../array_count_transitions_proof_manual.v", line 198, characters 6-9:
Error: Tactic failure: Cannot find witness.
```

The failing script destructed `l` and then tried to solve the two-or-more-elements case by rewriting `Zlength_cons` and calling `lia`:

```coq
destruct l.
- reflexivity.
- destruct l.
  + reflexivity.
  + rewrite Zlength_cons in H1.
    rewrite Zlength_cons in H1.
    pose proof (Zlength_nonneg l).
    lia.
```

That is the wrong shape: the initialization goal is not a length contradiction. For a nonempty list of any length, `sublist 0 1 l` is the singleton first element, and `array_count_transitions_spec` of a singleton is `0`. Planned edit: after `destruct l`, prove the nonempty branch by rewriting `sublist 0 1 (z :: l)` using `sublist_single 0 (z :: l) 0`, then `reflexivity`.

The immediate retry showed the rewrite direction needed to be forward, not backward:

```text
File ".../array_count_transitions_proof_manual.v", line 195, characters 6-90:
Error: Found no subterm matching "Znth 0 (z :: l) 0 :: nil" in the current goal.
```

The side goal after `replace` contains `sublist 0 1 (z :: l)`, so the proof must use:

```coq
rewrite (sublist_single 0 (z :: l) 0) by ...
```

not `rewrite <- ...`.

The next retry showed that even the forward rewrite is unnecessary in this proof state:

```text
Error: Found no subterm matching "sublist 0 (0 + 1) (z :: l)" in the current goal.
```

After `entailer!` and `destruct l`, the nonempty branch has already simplified the one-element prefix enough for `reflexivity`. Planned edit: leave the branch as just `reflexivity`.
