## 2026-04-23 02:36 Proof iteration 1

Fresh `symexec` succeeded and generated:

```text
string_fill_char_goal.v
string_fill_char_proof_auto.v
string_fill_char_proof_manual.v
string_fill_char_goal_check.v
```

The manual file contains two placeholders:

```coq
Lemma proof_of_string_fill_char_entail_wit_2 : string_fill_char_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_fill_char_return_wit_1 : string_fill_char_return_wit_1.
Proof. Admitted.
```

`string_fill_char_entail_wit_2` is the loop-preservation witness after executing `s[i] = c`. The left side already owns `CharArray.full s_pre (n_pre + 1) (replace_Znth i c_pre lr_2)`. The right side asks for an existential `lr` satisfying the next invariant at index `i + 1`. The intended witness is:

```coq
Exists (replace_Znth i c_pre lr_2).
```

The remaining pure facts are standard `replace_Znth` facts:

- length is unchanged;
- at the replaced index `i`, `Znth i` becomes `c_pre`;
- at any other index, `Znth` is unchanged.

For the prefix property `0 <= k < i + 1`, split on `k = i`. If equal, use the same-index replacement lemma. If different, then `k < i`, so use the old prefix invariant and the different-index lemma. For the suffix property `i + 1 <= k < n + 1`, the index is different from `i`, so use the different-index lemma and the old suffix invariant.

`string_fill_char_return_wit_1` is the final assignment `s[n] = 0`. The left side owns `CharArray.full s_pre (n_pre + 1) (replace_Znth n_pre 0 lr_2)`. Because the loop has exited, assumptions include `i_2 >= n_pre` and `i_2 <= n_pre`, so `i_2 = n_pre`. The intended postcondition witness is:

```coq
Exists (replace_Znth n_pre 0 lr_2).
```

The prefix indices satisfy `i < n_pre`, so they are different from `n_pre`; the old loop prefix property applies after rewriting unchanged cells. The terminator fact follows from the same-index replacement lemma. No annotation change is needed because both witnesses already contain the required heap shape and pure loop facts.

## 2026-04-23 02:37 Proof iteration 2

The first compile attempt was run without shell `set -e`, so the shell continued after Coq errors. The real failure was in `string_fill_char_proof_manual.v` line 97 while proving `string_fill_char_entail_wit_2`:

```text
Hk : i + 1 <= i < n_pre + 1
Unable to unify "Znth i l 0" with "c_pre".
```

This showed that `entailer!` produced the suffix-property subgoal before the prefix-property subgoal. My first script treated the first quantified subgoal as the prefix case and split on `k = i`; for the suffix subgoal, `k = i` is impossible because the hypothesis says `i + 1 <= k`. The fix is to make the first quantified subgoal the suffix proof: assert `k <> i` by `lia`, rewrite `replace_Znth` at a different index, and apply the old suffix invariant. The second quantified subgoal is then the prefix proof and keeps the split on `k = i`.

The next compile stopped in `string_fill_char_return_wit_1` at the first bullet with:

```text
Error: No product even after head-reduction.
```

Using `coqtop` after `entailer!` showed the return subgoal order is:

```coq
1. Znth n_pre (replace_Znth n_pre 0 lr_2) 0 = 0
2. forall i, 0 <= i < n_pre ->
     Znth i (replace_Znth n_pre 0 lr_2) 0 = c_pre
3. Zlength (replace_Znth n_pre 0 lr_2) = n_pre + 1
```

So the return proof must first close the terminator equality with `Znth_replace_Znth_same`, then introduce the quantified prefix index in the second bullet, then prove length preservation.
