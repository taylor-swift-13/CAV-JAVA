# Proof reasoning: array_move_zeroes_to_end

## 2026-04-22 06:13:57 +0800 - Manual obligations after successful symexec

Fresh `symexec` succeeded on the active annotated file and generated:

```text
coq/generated/array_move_zeroes_to_end_goal.v
coq/generated/array_move_zeroes_to_end_proof_auto.v
coq/generated/array_move_zeroes_to_end_proof_manual.v
coq/generated/array_move_zeroes_to_end_goal_check.v
```

The generated `proof_manual.v` currently has seven admitted obligations:

```coq
Lemma proof_of_array_move_zeroes_to_end_entail_wit_1 : array_move_zeroes_to_end_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_move_zeroes_to_end_entail_wit_2_1 : array_move_zeroes_to_end_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_move_zeroes_to_end_entail_wit_2_2 : array_move_zeroes_to_end_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_move_zeroes_to_end_entail_wit_3 : array_move_zeroes_to_end_entail_wit_3.
Proof. Admitted.

Lemma proof_of_array_move_zeroes_to_end_return_wit_1 : array_move_zeroes_to_end_return_wit_1.
Proof. Admitted.

Lemma proof_of_array_move_zeroes_to_end_which_implies_wit_1 : array_move_zeroes_to_end_which_implies_wit_1.
Proof. Admitted.

Lemma proof_of_array_move_zeroes_to_end_which_implies_wit_2 : array_move_zeroes_to_end_which_implies_wit_2.
Proof. Admitted.
```

The first-loop preservation witnesses are pure list/update obligations after `pre_process`. In the nonzero branch, the core goal is to use witness `replace_Znth write (Znth i lc_2 0) lc_2` and prove both:

```coq
write + 1 =
  Zlength (array_move_zeroes_to_end_nonzero (sublist 0 (i + 1) l))

forall k, 0 <= k < write + 1 ->
  Znth k (replace_Znth write (Znth i lc_2 0) lc_2) 0 =
  Znth k (array_move_zeroes_to_end_nonzero (sublist 0 (i + 1) l)) 0
```

The needed facts are that `sublist 0 (i+1) l = sublist 0 i l ++ Znth i l 0 :: nil`, and because the branch has `Znth i lc_2 0 <> 0` plus the invariant suffix fact `Znth i lc_2 0 = Znth i l 0`, the helper `array_move_zeroes_to_end_nonzero (xs ++ x :: nil) = array_move_zeroes_to_end_nonzero xs ++ x :: nil` applies.

In the zero branch, the same sublist-snoc fact combines with `Znth i l 0 = 0`, so the nonzero prefix is unchanged and the witness can simply be `lc_2`.

For the transition into the zero-fill loop, failed first-loop guard and invariant bounds give `i = n_pre`. Then `sublist 0 n_pre l = l`, so the first-loop prefix fact directly establishes the second-loop invariant at `write = Zlength(array_move_zeroes_to_end_nonzero(l))`.

For the return witness, failed second-loop guard gives `write_2 = n_pre`. The heap list `lc_2` has the nonzero prefix from `array_move_zeroes_to_end_nonzero(l)` and zeros for every suffix index up to `n_pre`. I will prove it equals `array_move_zeroes_to_end_spec(l)` by `list_eq_ext`: prefix indexes use `app_Znth1` and the invariant prefix fact; suffix indexes use `app_Znth2`, the invariant zero fact, and a helper lemma that every element of `array_move_zeroes_to_end_zeros` is zero. The spec length follows from a helper proving

```coq
Zlength (array_move_zeroes_to_end_nonzero xs) +
Zlength (array_move_zeroes_to_end_zeros xs) =
Zlength xs.
```

The two `which_implies` witnesses are heap-shape bridges. The first one should split `IntArray.full` at index `write` with `IntArray.full_split_to_missing_i`. The second should merge `IntArray.missing_i` and the updated zero cell back to `IntArray.full`, using witness `replace_Znth write 0 lc` and helper lemmas for `Zlength(replace_Znth ...)` and `Znth` at/everywhere except the replaced index. I will add these helper lemmas at the top of `proof_manual.v` and then replace the seven admitted proofs.

## 2026-04-22 06:18:12 +0800 - Proof compile result

After patching `coq/generated/array_move_zeroes_to_end_proof_manual.v`, the first proof compile attempt reached a syntax error in an inline induction:

```text
line 48, characters 33-35:
Error: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

The failing tactic was:

```coq
induction (sublist 0 i l) as [|x xs IH]; simpl.
```

I replaced those inline inductions with named helper lemmas:

```coq
Lemma amz_nonzero_snoc_nonzero :
  forall xs x,
    x <> 0 ->
    array_move_zeroes_to_end_nonzero (xs ++ [x]) =
    array_move_zeroes_to_end_nonzero xs ++ [x].

Lemma amz_nonzero_snoc_zero :
  forall xs x,
    x = 0 ->
    array_move_zeroes_to_end_nonzero (xs ++ [x]) =
    array_move_zeroes_to_end_nonzero xs.
```

The next compile found that this environment does not provide the attempted names `Znth_replace_Znth_diff`, `Znth_replace_Znth_same`, or `Zlength_replace_Znth`. I added local helper lemmas over `replace_nth` / `replace_Znth`:

```coq
Lemma amz_Znth_replace_Znth_same :
  forall (n: Z) (v: Z) (l: list Z) (d: Z),
    0 <= n < Zlength l ->
    Znth n (replace_Znth n v l) d = v.

Lemma amz_Znth_replace_Znth_other :
  forall (n: Z) (m: Z) (v: Z) (l: list Z) (d: Z),
    0 <= n ->
    0 <= m < Zlength l ->
    m <> n ->
    Znth m (replace_Znth n v l) d = Znth m l d.
```

A mechanical replacement accidentally renamed the helper declaration to `amz_amz_Znth_replace_Znth_same`; I corrected the declaration back to `amz_Znth_replace_Znth_same`.

Final replay compiled:

```text
original/array_move_zeroes_to_end.v
coq/generated/array_move_zeroes_to_end_goal.v
coq/generated/array_move_zeroes_to_end_proof_auto.v
coq/generated/array_move_zeroes_to_end_proof_manual.v
coq/generated/array_move_zeroes_to_end_goal_check.v
```

`logs/compile.log` ends with:

```text
compile_start 2026-04-22 06:17:45 +0800
compile_end 2026-04-22 06:17:51 +0800
```

`grep -RIn "Admitted\\.\\|^Axiom" coq/generated/array_move_zeroes_to_end_proof_manual.v` returned no matches, and non-`.v` Coq artifacts under `coq/` were removed after the successful replay.
