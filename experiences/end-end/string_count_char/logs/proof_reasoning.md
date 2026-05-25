## Proof iteration 1

Generated manual file: `output/verify_20260423_002212_string_count_char/coq/generated/string_count_char_proof_manual.v`.

After successful `symexec`, the manual file contained four admitted obligations:

```coq
Lemma proof_of_string_count_char_entail_wit_1 : string_count_char_entail_wit_1.
Proof. Admitted.

Lemma proof_of_string_count_char_entail_wit_2_1 : string_count_char_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_string_count_char_entail_wit_2_2 : string_count_char_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_string_count_char_entail_wit_3 : string_count_char_entail_wit_3.
Proof. Admitted.
```

The generated goals in `string_count_char_goal.v` are semantically provable from the annotation:

- `string_count_char_entail_wit_1` initializes the invariant by choosing `l1 = nil`, `l2 = l`, and using `string_count_char_spec nil c = 0`.
- `string_count_char_entail_wit_2_1` is the preservation case after the current character equals `c`; the next prefix is old `l1_2 ++ [x]`, and the spec increases by one.
- `string_count_char_entail_wit_2_2` is the preservation case after the current character does not equal `c`; the next prefix is old `l1_2 ++ [x]`, and the spec is unchanged.
- `string_count_char_entail_wit_3` is the loop-exit assertion; `Znth i (l ++ [0]) = 0` and the nonzero-prefix precondition imply `i = n`, after which the prefix length equals the full list length and the suffix must be empty.

The current proof stubs are not enough because the generated goals require explicit list-prefix reasoning: if `l = l1_2 ++ l2_2` and `Zlength l1_2 = i`, reading `Znth i (l ++ [0])` focuses on the head of `l2_2`; after one loop iteration the new prefix is `l1_2 ++ [x]`. This is the same proof pattern as `count_equal_to_k` for recursive count specs and `string_contains_char` for string-scan prefix/suffix decomposition.

Planned helper:

```coq
Lemma string_count_char_spec_app_single :
  forall (l : list Z) (x c : Z),
    string_count_char_spec (l ++ x :: nil) c =
    string_count_char_spec l c + (if Z.eq_dec x c then 1 else 0).
```

The witness proofs will use `pre_process` / `entailer!`, destruct the current suffix, select the existential prefix/suffix, rewrite with `app_Znth2` and `Zlength_app_cons`, and use `lia` for numeric bounds. No `Axiom` or `Admitted` will be added.

## Proof iteration 2

First compile replay:

```text
compiled: original/string_count_char.v
compiled: string_count_char_goal.v
compiled: string_count_char_proof_auto.v
File ".../string_count_char_proof_manual.v", line 89, characters 6-30:
Error: Found no subterm matching "Zlength (?M13738 ++ ?M13739 :: nil)"
in the current goal.
```

The failure is inside `proof_of_string_count_char_entail_wit_2_1` immediately after `entailer!` and existential selection:

```coq
Exists (l1_2 ++ x :: nil).
Exists xs.
entailer!.
+ rewrite Zlength_app_cons.
  lia.
```

The intended fact is the length side condition for the new processed prefix, but `entailer!` has already simplified or ordered the first remaining subgoal so that this rewrite is not always applicable. The fix is to leave the branch to `lia`, which already has `Zlength l1_2 = i` and the generated arithmetic context. The same overly-specific rewrite appears in the nonmatching branch `proof_of_string_count_char_entail_wit_2_2`, so I will replace both `rewrite Zlength_app_cons; lia` blocks with plain `lia`.

Second compile replay still failed at the same control point:

```text
File ".../string_count_char_proof_manual.v", line 89, characters 6-9:
Error: Tactic failure: Cannot find witness.
```

Using `coqtop` to stop immediately after existential selection showed that `entailer!` leaves several simple pure side conditions before the semantic spec equality, including `Zlength l = n` and `i < n`. The proof already has those facts as `Hlen_l` and `Hi_lt_n`, but a bare bullet with `lia` can be routed to the wrong generated pure goal before all simple side conditions are discharged. I will change the two preservation witnesses from:

```coq
entailer!.
```

to:

```coq
entailer!; try lia.
```

This lets the standard arithmetic side conditions close immediately, leaving only the spec-update and append-reassociation goals for the explicit bullets.

The `coqtop` state after `Exists (l1_2 ++ x :: nil); Exists xs` showed the first non-arithmetic pure goal is actually the append reassociation:

```coq
l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs
```

The earlier script tried to solve a length or arithmetic side condition first, which explains the `Cannot find witness` at the first bullet. I will order the explicit bullets as append reassociation first, then the prefix length side condition, then the semantic spec update. The same ordering applies to both the matching and nonmatching preservation witnesses.

That ordering still depended on the exact order in which `entailer!` emitted pure subgoals; the next compile reported that the first bullet was not the append equality either:

```text
File ".../string_count_char_proof_manual.v", line 89, characters 6-26:
Error: Found no subterm matching "(?M13739 ++ ?M13740) ++ ?M13741"
in the current goal.
```

To avoid relying on subgoal order, I will prove the three pure bridge facts before calling `entailer!`:

```coq
Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs
Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1
Hspec_next : ret +/- update = string_count_char_spec (l1_2 ++ x :: nil) c_pre
```

Then the final `Exists ...; Exists ...; entailer!` step can consume named facts regardless of the generated pure-goal order.

The next replay compiled both preservation witnesses and failed in the loop-exit witness:

```text
File ".../string_count_char_proof_manual.v", line 222, characters 4-21:
Error: Found no subterm matching "?M9609 ++ nil" in the current goal.
```

The failing block was after `entailer!` in `proof_of_string_count_char_entail_wit_3`:

```coq
Exists l1_2.
Exists l2_2.
entailer!.
subst ret.
subst l.
destruct l2_2.
- rewrite app_nil_r.
```

This again depends on generated subgoal order. The cleaner exit proof is to prove before `entailer!` that the old prefix is already the whole list: from `i = n`, `Zlength l1_2 = i`, `Zlength l = n`, and `l = l1_2 ++ l2_2`, the suffix must be empty. Then choose `l1 = l` and `l2 = nil` directly, with `ret = string_count_char_spec l c_pre` already established as a named fact.

After adding the direct `l/nil` choice, compile failed at the final `rewrite app_nil_r`, meaning `entailer!` had not left the append equality as the active subgoal. I will make that final cleanup order-independent with `entailer!; try rewrite app_nil_r; try reflexivity`.

The remaining open goal after that cleanup was a spatial store equality:

```coq
&( "i") # Int |-> Zlength l1_2 |-- &( "i") # Int |-> n
```

At this point `Hi_eq_n : Zlength l1_2 = n` is already in context, but `entailer!` does not rewrite the store payload automatically. I will explicitly replace `Zlength l1_2` with `n` before selecting the exit assertion witnesses.
