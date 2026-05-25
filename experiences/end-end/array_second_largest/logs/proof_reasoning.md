# Proof Reasoning

## Manual witness iteration 1

Fresh `symexec` succeeded on the current active annotated file and generated:

```text
coq/generated/array_second_largest_goal.v
coq/generated/array_second_largest_proof_auto.v
coq/generated/array_second_largest_proof_manual.v
coq/generated/array_second_largest_goal_check.v
```

The generated manual file contains four admitted obligations:

```coq
Lemma proof_of_array_second_largest_entail_wit_1_1 : array_second_largest_entail_wit_1_1.
Proof. Admitted.

Lemma proof_of_array_second_largest_entail_wit_1_2 : array_second_largest_entail_wit_1_2.
Proof. Admitted.

Lemma proof_of_array_second_largest_entail_wit_2_1 : array_second_largest_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_second_largest_entail_wit_2_2 : array_second_largest_entail_wit_2_2.
Proof. Admitted.
```

The corresponding goals in `array_second_largest_goal.v` are all assertion-level existential entailments. For `entail_wit_1_1`, the branch has `Znth 1 l 0 > Znth 0 l 0`, so the witnesses are `second = 0`, `top = 1`. For `entail_wit_1_2`, the branch has `Znth 1 l 0 <= Znth 0 l 0`; pairwise distinctness and `n >= 2` imply the strict opposite order, so the witnesses are `second = 1`, `top = 0`. For `entail_wit_2_1`, the new element is larger than old `max1`, so after the loop body `top = i` and `second = old top_2`. For `entail_wit_2_2`, the new element is between old `max1` and old `max2`, so after the loop body `top = old top_2` and `second = i`.

Planned proof edit: use `pre_process`, then QCP assertion-level `Exists` in the order shown by the goal (`EX second top`), then `entailer!`. The remaining pure goals are bounded integer facts and one quantified prefix fact; those will be discharged by a small `intros` plus `lia`/case split on whether the quantified index is the newly appended `i` or lies in the old prefix.

The first compile attempt reached `array_second_largest_proof_manual.v` and failed at line 29:

```text
Error: Expects a disjunctive pattern with 1 branch or a conjunctive pattern
made of 0 patterns.
```

The failing code used `assert (k = 0 \/ k = 1) by lia.` and then destructed `H`, but `H` was already a generated hypothesis from `pre_process`, not the unnamed assertion. The fix is mechanical and proof-local: name each case assertion explicitly, e.g. `assert (Hcase : k = 0 \/ k = 1) by lia`, then destruct `Hcase`.

The next compile failed in `entail_wit_1_2` because the script guessed the pairwise-distinct hypothesis name incorrectly:

```text
The expression "H2" of type "Zlength l = n_pre" cannot be applied to the term "0"
```

`coqtop` showed the actual context after `pre_process`:

```coq
H  : Znth 1 l 0 <= Znth 0 l 0
H0 : 2 <= n_pre
H1 : n_pre <= 2147483647
H2 : Zlength l = n_pre
H3 : forall i j : Z, 0 <= i < j /\ j < n_pre -> Znth i l 0 <> Znth j l 0
```

It also showed that after `Exists 1 0; entailer!`, the first subgoal is the quantified prefix bound and the second subgoal is `Znth 0 l 0 > Znth 1 l 0`. The fix is to prove the prefix subgoal first by `k = 1`, then use `H3 0 1` plus `H` to prove the strict ordering.

After the invariant was strengthened with `Zlength(l) == n` and pairwise distinctness, `symexec` regenerated the manual proof file. The final proof uses:

```coq
Exists 0 1.      (* initialization branch: l[1] > l[0] *)
Exists 1 0.      (* initialization branch: l[1] <= l[0] *)
Exists top_2 i.  (* new element becomes top; old top becomes second *)
Exists i top_2.  (* new element becomes second; old top remains top *)
```

For the final `entail_wit_2_2` strictness side condition, the script uses the preserved pairwise-distinct hypothesis:

```coq
pose proof (Hdist top_2 i ltac:(lia)) as Hneq;
rewrite Htop in Hneq;
lia
```

This proves that `Znth i l 0` cannot equal `max1`, because `max1` is stored at old `top_2` and `top_2 < i`. The full compile replay then passed:

```text
compiled=array_second_largest_goal.v
compiled=array_second_largest_proof_auto.v
compiled=array_second_largest_proof_manual.v
compiled=array_second_largest_goal_check.v
compile_status=0
```

`rg -n "Admitted\.|^\s*Axiom\b" coq/generated/array_second_largest_proof_manual.v` returned no matches.
