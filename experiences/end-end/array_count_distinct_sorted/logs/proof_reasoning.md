# Proof Reasoning

## Manual witness analysis after first successful symexec

Fresh `symexec` succeeded on `annotated/verify_20260422_030111_array_count_distinct_sorted.c` and generated:

```text
coq/generated/array_count_distinct_sorted_goal.v
coq/generated/array_count_distinct_sorted_proof_auto.v
coq/generated/array_count_distinct_sorted_proof_manual.v
coq/generated/array_count_distinct_sorted_goal_check.v
```

The generated manual proof file contains five admitted lemmas:

```coq
Lemma proof_of_array_count_distinct_sorted_entail_wit_1 : array_count_distinct_sorted_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_count_distinct_sorted_entail_wit_2_1 : array_count_distinct_sorted_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_count_distinct_sorted_entail_wit_2_2 : array_count_distinct_sorted_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_count_distinct_sorted_return_wit_1 : array_count_distinct_sorted_return_wit_1.
Proof. Admitted.

Lemma proof_of_array_count_distinct_sorted_return_wit_2 : array_count_distinct_sorted_return_wit_2.
Proof. Admitted.
```

I probed each theorem with `coqtop` using `pre_process; entailer!`.  The separation logic and arithmetic portions are discharged automatically; the remaining subgoals are pure list/spec equalities:

```coq
1 = array_count_distinct_sorted_spec (sublist 0 1 l)

count + 1 =
  array_count_distinct_sorted_spec (sublist 0 (i_2 + 1) l)

count =
  array_count_distinct_sorted_spec (sublist 0 (i_2 + 1) l)

0 = array_count_distinct_sorted_spec l

count = array_count_distinct_sorted_spec l
```

The key available hypotheses for the loop-step witnesses are:

```coq
H  : Znth i_2 l 0 <> Znth (i_2 - 1) l 0    (* increment branch *)
H  : Znth i_2 l 0 = Znth (i_2 - 1) l 0     (* non-increment branch *)
H0 : i_2 < n_pre
H1 : 1 <= i_2
H5 : count = array_count_distinct_sorted_spec (sublist 0 i_2 l)
H9 : Zlength l = n_pre
```

The current proof script cannot be just `entailer!` because Coq needs explicit facts that `sublist 0 (i+1) l` is `sublist 0 i l ++ [Znth i l 0]`, and that appending the next element changes the recursive distinct-count spec according to equality with the previous last element.  I will add local helper lemmas directly in `array_count_distinct_sorted_proof_manual.v`:

```coq
sublist_prefix_snoc_Z :
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0]

array_count_distinct_sorted_spec_snoc_nonempty :
  xs <> [] ->
  array_count_distinct_sorted_spec (xs ++ [y]) =
  array_count_distinct_sorted_spec xs +
  (if Z.eq_dec y (last xs d) then 0 else 1)
```

Then each loop preservation witness can rewrite by `sublist_prefix_snoc_Z`, rewrite the snoc-spec lemma, use `last (sublist 0 i_2 l) 0 = Znth (i_2 - 1) l 0`, destruct `Z.eq_dec`, and finish with the branch equality/disequality plus `lia`.  The return witnesses should finish by `Zlength_nil_inv` for `n == 0` and `sublist_self` after deriving `i_2 = n_pre` for the nonzero path.

## Proof repair details and final state

I edited only `output/verify_20260422_030111_array_count_distinct_sorted/coq/generated/array_count_distinct_sorted_proof_manual.v`.  The first proof attempt used singleton list notation such as:

```coq
sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0]
xs <> []
```

This failed under `Local Open Scope sac` because `[x]` and `[]` were parsed as assertion notation rather than `list Z` notation.  The concrete compile error was:

```text
The term "[Znth i l 0]" has type "Z -> Prop"
while it is expected to have type "list Z".
```

The fix was to avoid list bracket notation in this generated proof file and write singletons and nil explicitly:

```coq
sublist 0 (i + 1) l = sublist 0 i l ++ (Znth i l 0 :: nil)
xs <> nil
```

The helper lemma `sublist_prefix_snoc_Z` also needed explicit `Zlength_correct` rewriting for the library lemma side condition:

```coq
rewrite (@sublist_split Z 0 (i + 1) i l).
2: lia.
2: rewrite <- Zlength_correct; lia.
```

The final proof file now proves all five manual witnesses.  The loop-step witnesses use:

```coq
rewrite H5.
rewrite sublist_prefix_snoc_Z by lia.
rewrite array_count_distinct_sorted_spec_snoc_nonempty with (d := 0).
rewrite last_sublist_prefix_Z by lia.
destruct (Z.eq_dec (Znth i_2 l 0) (Znth (i_2 - 1) l 0)); lia.
```

The final return witness derives `i_2 = n_pre`, rewrites the invariant equality, and normalizes the full prefix with `sublist_self`; the length equality had to be used symmetrically:

```coq
rewrite (sublist_self l n_pre) by (symmetry; exact H8).
```

Final compile replay from `QualifiedCProgramming/SeparationLogic` succeeded for:

```text
original/array_count_distinct_sorted.v
coq/generated/array_count_distinct_sorted_goal.v
coq/generated/array_count_distinct_sorted_proof_auto.v
coq/generated/array_count_distinct_sorted_proof_manual.v
coq/generated/array_count_distinct_sorted_goal_check.v
```

`rg -n "Admitted\.|^\s*Axiom\b" coq/generated/array_count_distinct_sorted_proof_manual.v` produced no matches.  Non-`.v` Coq build artifacts under the workspace `coq/` directory were removed after compilation.
