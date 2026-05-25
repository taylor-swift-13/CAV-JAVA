## 2026-04-23 00:00 Manual proof iteration 1

Fresh `symexec` generated `coq/generated/string_copy_goal.v`, `string_copy_proof_auto.v`, `string_copy_proof_manual.v`, and `string_copy_goal_check.v`. The manual file contains three obligations:

```coq
Lemma proof_of_string_copy_entail_wit_1 : string_copy_entail_wit_1.
Lemma proof_of_string_copy_entail_wit_2 : string_copy_entail_wit_2.
Lemma proof_of_string_copy_return_wit_1 : string_copy_return_wit_1.
```

The current generated VC body carries the strengthened contract fact:

```coq
forall k : Z, 0 <= k /\ k < n -> Znth k l 0 <> 0
```

This makes the final return witness semantically provable: from `Znth i (l ++ 0 :: nil) 0 = 0`, `0 <= i`, and `i <= n`, prove `i = n` by contradiction on `i < n`; then use the copied-prefix fact to prove `l1 = l`, destruct the one-element destination suffix `d1`, and normalize `replace_Znth`.

I checked the archived completed proof for `string_copy`. Its witness names and proof obligations match this current VC shape: initialization chooses `l1 = nil` and `d1 = d`; loop preservation destructs the destination suffix and chooses `l1_2 ++ [Znth i l 0]`; return derives `i = n`, `l1 = l`, and reduces the final destination list. I will reuse that proof skeleton with only the current import path:

```coq
From SimpleC.EE.CAV.verify_20260422_235720_string_copy Require Import string_copy_goal.
```

No `Axiom` or `Admitted` will be added. After editing, the next check is compiling `string_copy_proof_manual.v`; if binder names or goal order differ from the archive, I will inspect the exact Coq proof state and adjust the script locally.

## 2026-04-23 00:03 Manual proof iteration 2

The first compile attempt failed in `proof_of_string_copy_entail_wit_2` because the archived proof depended on generated hypothesis names and post-`entailer!` pure-goal order:

```text
File ".../string_copy_proof_manual.v", line 98:
Unable to unify "Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1"
with "Znth k (l1_2 ++ Znth i l 0 :: nil) 0 = Znth k l 0".
```

The current VC named the source length fact `H10`; the prefix-equality hypothesis was `H6`. I first swapped the two bullets, but the next compile showed the second remaining goal was not a quantified predicate:

```text
Error: No product even after head-reduction.
```

To avoid relying on fragile goal order, I changed the proof to establish the three required preservation facts before `entailer!`:

```coq
Hlen_l1_new :
  Zlength (l1_2 ++ cons (Znth i l 0) nil) = i + 1
Hlen_l0 :
  Zlength l0 = n + 1 - (i + 1)
Hprefix_new :
  forall k, 0 <= k < i + 1 ->
    Znth k (l1_2 ++ cons (Znth i l 0) nil) 0 = Znth k l 0
```

This keeps the separation side simple: after rewriting the destination array with `Hdst`, `entailer!` can consume the named pure facts and frame the two `CharArray.full` resources.

The next compile failed in `proof_of_string_copy_return_wit_1` for the same generated-name reason:

```text
Illegal application: the expression "H10" of type
"Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1"
cannot be applied to the term "i".
```

I replaced the stale direct call to `H10` with a shape-based `match goal` that selects the nonzero-prefix predicate:

```coq
match goal with
| Hnz : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
    apply Hnz; lia
end
```

The final compile failure was also a stale hypothesis choice while proving `l1 = l`; the copied-prefix equality is `H6`, not the nonzero predicate `H5`. After switching that line to `apply H6`, the full compile replay succeeded:

```text
compiled string_copy_goal.v
compiled string_copy_proof_auto.v
compiled string_copy_proof_manual.v
compiled string_copy_goal_check.v
```

Final proof status: `string_copy_proof_manual.v` contains no `Admitted.` and no local `Axiom`. The manual proof is complete, and `goal_check.v` compiles under the current workspace logic path.
