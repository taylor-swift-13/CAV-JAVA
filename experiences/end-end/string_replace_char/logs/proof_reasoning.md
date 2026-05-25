# Proof Reasoning

## 2026-04-23 retry manual witnesses

After the active annotated parser repair, `symexec` succeeded and generated:

- `coq/generated/string_replace_char_goal.v`
- `coq/generated/string_replace_char_proof_auto.v`
- `coq/generated/string_replace_char_proof_manual.v`
- `coq/generated/string_replace_char_goal_check.v`

The generated manual file contains four admitted witnesses:

```coq
Lemma proof_of_string_replace_char_entail_wit_1 : string_replace_char_entail_wit_1.
Proof. Admitted.

Lemma proof_of_string_replace_char_entail_wit_2_1 : string_replace_char_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_string_replace_char_entail_wit_2_2 : string_replace_char_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_string_replace_char_return_wit_1 : string_replace_char_return_wit_1.
Proof. Admitted.
```

The corresponding goals in `string_replace_char_goal.v` are prefix/suffix list-shape obligations:

- `string_replace_char_entail_wit_1`: initialize the loop invariant by choosing `l1 = nil` and `l2 = l ++ 0 :: nil`.
- `string_replace_char_entail_wit_2_1`: after the current character equals `old_c_pre` and the program writes `new_c_pre`, rebuild the invariant with processed prefix `l1_2 ++ new_c_pre :: nil` and remaining suffix `xs`.
- `string_replace_char_entail_wit_2_2`: after the current character is nonzero and not `old_c_pre`, rebuild the invariant with processed prefix `l1_2 ++ x :: nil`, where `x` is the head of the old suffix.
- `string_replace_char_return_wit_1`: from break condition `Znth i_2 (l1 ++ l2) 0 = 0` and payload nonzero facts, first prove `i_2 = n`, then prove the suffix is exactly `0 :: nil`, and choose `lr = l1`.

The key proof blocker is not separation logic ownership; it is normalizing `Znth` over `app`, `replace_Znth` at the prefix boundary, and the one-cell suffix at loop exit. The proof will add local helper lemmas in `string_replace_char_proof_manual.v`, following the same local-helper pattern used by `output/verify_20260423_032238_string_remove_char_to_output/coq/generated/string_remove_char_to_output_proof_manual.v` (`current_head_after_prefix` and `replace_at_prefix_end`).

Planned proof structure:

1. Add helper lemmas:
   - `replace_at_prefix_end` for `replace_Znth i x (pre ++ old :: tail) = pre ++ x :: tail`.
   - `current_head_after_prefix` for reading the head of the suffix at index `i`.
   - `suffix_head_from_app` to recover the head value of `l2` from `Znth i (l1 ++ l2)`.
2. For each loop-preservation witness, prove `i < n`; if `i = n`, the current read would be the invariant terminator `0`, contradicting the branch condition `Znth i (...) <> 0`.
3. Destruct the suffix `l2_2`; the empty case contradicts `Zlength(l2_2) = n + 1 - i` together with `i < n`.
4. Use `Exists xs (l1_2 ++ value :: nil)` and `entailer!`; handle the two prefix cases `t < i` and `t = i` explicitly.
5. For return, derive `i_2 = n` from the same nonzero-payload argument, destruct `l2`, and show the only possible suffix is `0 :: nil`.

## 2026-04-23 retry proof completion

The manual proof was completed in `output/verify_20260423_033114_string_replace_char/coq/generated/string_replace_char_proof_manual.v`.

Added local helper lemmas:

```coq
Lemma current_head_after_prefix :
  forall (pre xs : list Z) (x i d : Z),
    Zlength pre = i ->
    Znth i (pre ++ x :: xs) d = x.

Lemma replace_at_prefix_end :
  forall (pre tail : list Z) (old i x : Z),
    Zlength pre = i ->
    replace_Znth i x (pre ++ old :: tail) =
    pre ++ x :: tail.

Lemma Znth_cons_succ :
  forall (xs : list Z) (x k d : Z),
    0 <= k ->
    Znth (1 + k) (x :: xs) d = Znth k xs d.
```

Representative proof blocker and repair:

- In `entail_wit_2_1`, the branch `s[i] == old_c` needs to prove the new prefix element is `new_c_pre` and that the impossible preservation implication is discharged by contradiction. The proof specializes the suffix relation at `0` to obtain `x = Znth i l 0`, then combines it with `x = old_c_pre`.
- In `entail_wit_2_2`, the branch `s[i] != old_c` keeps the head value `x`; the proof uses the same suffix specialization at `0` to prove `x = Znth i l 0` and derives nonzero from the original payload nonzero precondition.
- In `return_wit_1`, the break read `Znth i_2 (l1 ++ l2) 0 = 0` plus the suffix relation and original payload nonzero fact first proves `i_2 = n`. Then `Zlength l2 = 1` and `Znth 0 l2 0 = 0` force `l2 = 0 :: nil`, so the postcondition can choose `lr = l1`.

Compile result after proof edits:

```text
coqc string_replace_char_proof_manual.v: success
coqc string_replace_char_goal_check.v: success
```

`proof_manual.v` contains no `Admitted.` and no local `Axiom` declaration. The only `Axioms` text is the existing imported module name in `From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.`
