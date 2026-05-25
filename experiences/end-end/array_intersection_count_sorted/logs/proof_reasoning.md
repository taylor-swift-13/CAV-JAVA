## 2026-04-22 05:17:14 CST - Manual proof plan after successful symexec

Fresh `symexec` succeeded on the latest active annotated file and generated six manual obligations in `coq/generated/array_intersection_count_sorted_proof_manual.v`:

```coq
Lemma proof_of_array_intersection_count_sorted_entail_wit_1 : array_intersection_count_sorted_entail_wit_1.
Lemma proof_of_array_intersection_count_sorted_entail_wit_2_1 : array_intersection_count_sorted_entail_wit_2_1.
Lemma proof_of_array_intersection_count_sorted_entail_wit_2_2 : array_intersection_count_sorted_entail_wit_2_2.
Lemma proof_of_array_intersection_count_sorted_entail_wit_2_3 : array_intersection_count_sorted_entail_wit_2_3.
Lemma proof_of_array_intersection_count_sorted_return_wit_1 : array_intersection_count_sorted_return_wit_1.
Lemma proof_of_array_intersection_count_sorted_return_wit_2 : array_intersection_count_sorted_return_wit_2.
```

The corresponding `goal.v` definitions show that the separation-logic heap part is unchanged `IntArray.full` ownership. The hard pure obligations are:

```coq
0 + array_intersection_count_sorted_spec (sublist 0 n_pre la) (sublist 0 m_pre lb)
  = array_intersection_count_sorted_spec la lb

count + array_intersection_count_sorted_spec (sublist i_3 n_pre la) (sublist j_3 m_pre lb)
  = array_intersection_count_sorted_spec la lb
```

after moving one or both suffix starts, and at return:

```coq
count + array_intersection_count_sorted_spec (sublist i_3 n_pre la) (sublist j_3 m_pre lb)
  = array_intersection_count_sorted_spec la lb
|--
count = array_intersection_count_sorted_spec la lb
```

when either `j_3 = m_pre` or `i_3 = n_pre`.

Planned proof structure:

- Add a helper `array_intersection_sublist_cons` that rewrites a nonempty suffix `sublist lo hi l` to `Znth lo l 0 :: sublist (lo + 1) hi l`.
- Add `array_intersection_spec_nil_r`, because when the second list suffix is empty, the nested `count_with_b` part returns zero for every first-list suffix.
- Add three suffix-step helpers matching the C branches:
  - equal heads: one match plus both suffixes advance;
  - `la[i] < lb[j]`: the first suffix advances;
  - `la[i] > lb[j]`: the second suffix advances.
- In each generated witness, unfold the witness, run `entailer!`, rewrite the invariant equality with the relevant helper, and finish the arithmetic with `lia`.

This is a proof-stage issue rather than an annotation issue: the generated VCs contain the exact suffix semantic invariant, the current branch comparison facts, all suffix bounds, and both array ownership predicates. The remaining work is proving that the recursive Coq spec reduces consistently with those branch facts.

## 2026-04-22 05:18 CST - First compile failure in helper length side condition

The first full compile chain reached `coq/generated/array_intersection_count_sorted_proof_manual.v` and failed before any generated witness body:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 30, characters 46-49:
Error: Tactic failure:  Cannot find witness.
```

The failing line was:

```coq
rewrite (sublist_split lo hi (lo + 1) l) by lia.
```

The issue is not the loop invariant. The generated proof has the required suffix bounds, but the local helper `array_intersection_sublist_cons` states its upper bound as `hi <= Zlength l`, while the imported `sublist_split` lemma asks for `mid <= hi <= Z.of_nat (length l)`. The next edit will keep the same helper shape but explicitly bridge `Zlength l` to `Z.of_nat (length l)` using `Zlength_correct` before calling `sublist_split` and `sublist_single`.

## 2026-04-22 05:19 CST - Comparison helper branch script was too loose

After fixing the length bridge, `coqc` next failed in `array_intersection_step_eq`:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 65, characters 2-14:
Error: No such goal.
```

The failing fragment was:

```coq
destruct (Z.eq_dec (Znth i la 0) (Znth j lb 0)); try lia.
reflexivity.
```

In the equal branch, `lia` was strong enough to solve the reflexive arithmetic/list expression, so the subsequent `reflexivity` had no remaining goal. The next edit makes all comparison branches explicit: equal branch uses `reflexivity`, impossible branches use `lia`, and the less-than boolean split uses `Z.ltb_spec0` with one branch per case.

## 2026-04-22 05:20 CST - Numbered invariant hypothesis was unstable

The next manual compile failure was:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 130, characters 2-16:
Error: Found no subterm matching "Znth ?z0 la 0" in the current goal.
```

Line 130 was `rewrite <- H14.` in `proof_of_array_intersection_count_sorted_entail_wit_2_1`. After `entailer!`, the generated hypothesis numbering did not match the earlier read of `goal.v`; `H14` was a sortedness fact rather than the semantic invariant

```coq
count + array_intersection_count_sorted_spec (sublist i_3 n_pre la) (sublist j_3 m_pre lb)
  = array_intersection_count_sorted_spec la lb
```

The next edit removes numbered references for the semantic invariant and instead uses `match goal` to select the hypothesis by its formula shape. This is more stable across `entailer!` naming differences.

## 2026-04-22 05:21 CST - Return witness matcher was too specific

After replacing numbered branch references, the branch witnesses compiled and the next failure moved to `proof_of_array_intersection_count_sorted_return_wit_1`:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 174, characters 2-290:
Error: No matching clauses for match.
```

The failed matcher required the invariant to contain exactly `sublist m_pre m_pre lb` after `subst j_3`, but the proof state did not expose that term in that exact syntactic shape. The semantic fact is still present; the robust approach is to match any hypothesis of shape

```coq
count + array_intersection_count_sorted_spec ?A ?B =
  array_intersection_count_sorted_spec la lb
```

and then rewrite `sublist_nil` inside that hypothesis using the available arithmetic equalities. The same general matcher will be used for the `i_3 = n_pre` return branch.

`coqtop` showed that after `entailer!` the return witnesses expose stable semantic invariant names:

```coq
(* return_wit_1 *)
H16 :
  count + array_intersection_count_sorted_spec (sublist i_3 n_pre la)
    (sublist j_3 m_pre lb) = array_intersection_count_sorted_spec la lb

(* return_wit_2 *)
H15 :
  count + array_intersection_count_sorted_spec (sublist i_3 n_pre la)
    (sublist j_3 m_pre lb) = array_intersection_count_sorted_spec la lb
```

The generic matcher still failed because the proof-state term did not match the pattern in this local tactic context. The next edit uses these two observed names for the return witnesses only, while keeping shape-based matching in the branch witnesses where it already compiled.

## 2026-04-22 05:22 CST - `sublist_nil` needed targeted rewrite on return

Using `H16` directly moved the failure to:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 174, characters 32-35:
Error: Tactic failure:  Cannot find witness.
```

The failing tactic was:

```coq
rewrite sublist_nil in H16 by lia.
```

`H16` contains two sublists. In `return_wit_1`, only the second suffix `sublist m_pre m_pre lb` is empty; the first suffix `sublist i_3 n_pre la` is not empty because this branch still has `i_3 < n_pre`. The unrestricted rewrite tried to use `sublist_nil` on the wrong occurrence. The next edit targets only the exhausted suffix with:

```coq
replace (sublist m_pre m_pre lb) with (@nil Z) in H16 by ...
```

and similarly targets `sublist n_pre n_pre la` in `return_wit_2`.
