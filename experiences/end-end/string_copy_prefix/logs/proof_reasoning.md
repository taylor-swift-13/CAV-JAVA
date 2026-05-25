## 2026-04-23 manual witnesses after successful symexec

Fresh `symexec` completed with `symexec_status=0` and generated:

```text
output/verify_20260423_000831_string_copy_prefix/coq/generated/string_copy_prefix_goal.v
output/verify_20260423_000831_string_copy_prefix/coq/generated/string_copy_prefix_proof_auto.v
output/verify_20260423_000831_string_copy_prefix/coq/generated/string_copy_prefix_proof_manual.v
output/verify_20260423_000831_string_copy_prefix/coq/generated/string_copy_prefix_goal_check.v
```

The manual file contains three admitted obligations:

```coq
Lemma proof_of_string_copy_prefix_entail_wit_1 : string_copy_prefix_entail_wit_1.
Lemma proof_of_string_copy_prefix_entail_wit_2 : string_copy_prefix_entail_wit_2.
Lemma proof_of_string_copy_prefix_return_wit_1 : string_copy_prefix_return_wit_1.
```

Current VC shapes:

```coq
string_copy_prefix_entail_wit_1:
  CharArray.full src_pre (n + 1) (l ++ 0 :: nil) **
  CharArray.full dst_pre (k_pre + 1) d
  |-- EX d1 l1, ... CharArray.full dst_pre (k_pre + 1) (l1 ++ d1)
```

This is loop invariant initialization. Choose `l1 = nil` and `d1 = d`; the destination shape becomes `nil ++ d`, and `CharArray.full_length` supplies the list length fact if needed.

```coq
string_copy_prefix_entail_wit_2:
  CharArray.full dst_pre (k_pre + 1)
    (replace_Znth i_2 (Znth i_2 (l ++ 0 :: nil) 0) (l1_2 ++ d1_2))
  |-- EX d1 l1, ... CharArray.full dst_pre (k_pre + 1) (l1 ++ d1)
```

This is loop preservation after `dst[i] = src[i]` and before the `for` increment state is re-established. Since `i_2 < k_pre <= n`, `Znth i_2 (l ++ [0]) 0 = Znth i_2 l 0`. Destruct `d1_2` to expose its head cell, normalize `replace_Znth` over `l1_2 ++ z :: l0`, and choose `l1 = l1_2 ++ [Znth i_2 l 0]`, `d1 = l0`.

```coq
string_copy_prefix_return_wit_1:
  CharArray.full dst_pre (k_pre + 1)
    (replace_Znth k_pre 0 (l1 ++ d1))
  |-- CharArray.full dst_pre (k_pre + 1)
    (sublist 0 k_pre l ++ 0 :: nil)
```

This is final postcondition reconstruction. Loop exit gives `i_2 >= k_pre` and the invariant gives `i_2 <= k_pre`, so `i_2 = k_pre`. The invariant provides `Zlength l1 = k_pre`, `Zlength d1 = 1`, and pointwise equality between `l1` and `l` on indices `< k_pre`; using `list_eq_ext`, `Zlength_sublist`, and `Znth_sublist`, prove `l1 = sublist 0 k_pre l`. Then destruct the one-cell `d1` and normalize the final `replace_Znth` at the suffix head.

The proof will reuse the verified `string_copy` pattern but with `k_pre` as the final boundary instead of deriving `i = n` from the source terminator.

## 2026-04-23 proof iteration 2

First full compile reached `string_copy_prefix_proof_manual.v` and failed at the first witness:

```text
File ".../string_copy_prefix_proof_manual.v", line 33, characters 2-3:
Error: [Focus] Wrong bullet -: No more goals.
```

The failing proof fragment was:

```coq
entailer!.
- rewrite Zlength_correct.
  lia.
```

For this bounded prefix variant, after choosing `d1 = d` and `l1 = nil`, the preceding `prop_apply CharArray.full_length` and pure context are sufficient for `entailer!` to close all subgoals. The copied bullet was needed in the older `string_copy` proof but is stale here. I will remove the bullet and leave `entailer!.` as the end of `proof_of_string_copy_prefix_entail_wit_1`.

## 2026-04-23 proof iteration 3

The next compile reached `proof_of_string_copy_prefix_entail_wit_2` and failed:

```text
File ".../string_copy_prefix_proof_manual.v", line 57, characters 4-29:
Error: Found no subterm matching "Zlength nil" in H4.
```

The copied proof assumed the destination suffix length hypothesis was named `H4`, but in the current generated prefix-copy VC, `pre_process` names it `H8`:

```coq
H8 : Zlength d1_2 = k_pre + 1 - i_2
```

After `destruct d1_2`, the nil branch has:

```coq
H8 : Zlength nil = k_pre + 1 - i_2
```

and the cons branch has:

```coq
H8 : Zlength (z :: l0) = k_pre + 1 - i_2
```

The repair is to avoid hard-coded hypothesis numbers and use `match goal` to find the `Zlength nil` or `Zlength (z :: l0)` hypothesis. The same change applies to the return witness's one-cell suffix proof.

## 2026-04-23 proof iteration 4

Compile then failed in the same witness:

```text
File ".../string_copy_prefix_proof_manual.v", line 87, characters 4-73:
Error: No matching clauses for match.
```

The problematic fragment was trying to match the rewritten suffix length as exactly:

```coq
Hcons : 1 + Zlength l0 = _
```

but Coq's simplification can leave an equivalent shape that does not syntactically match this pattern. I will make the proof more stable by first copying the cons-suffix length into a named fact:

```coq
assert (Hlen_d1_cons : Zlength (z :: l0) = k_pre + 1 - i_2) by exact ...
rewrite Zlength_cons in Hlen_d1_cons.
```

Then later length goals can use `Hlen_d1_cons` directly with `lia`, avoiding brittle goal-shape matching.

## 2026-04-23 proof iteration 5

Compile then reached `proof_of_string_copy_prefix_return_wit_1` and failed while proving `l1 = sublist 0 k_pre l`:

```text
Unable to unify "Zlength l = n" with
"Znth k l1 0 = Znth (k + 0) l 0".
```

At that proof point the relevant hypotheses are:

```coq
H10 : forall j_2 : Z,
        0 <= j_2 < Zlength l1 -> Znth j_2 l1 0 = Znth j_2 l 0
Hi_eq_k : Zlength l1 = k_pre
```

The script accidentally used `H6`, which is only the length fact `Zlength l = n`. The repair is to apply `H10` after rewriting `Znth_sublist`, with `Hi_eq_k` and the loop bounds discharging the range side conditions.

## 2026-04-23 proof iteration 6

The return witness then failed on a harmless arithmetic normalization after `Znth_sublist`:

```text
Unable to unify "k + 0" with "k".
```

After rewriting `Znth k (sublist 0 k_pre l) 0`, Coq leaves the right side as `Znth (k + 0) l 0`. The invariant prefix hypothesis gives `Znth k l1 0 = Znth k l 0`. I will explicitly normalize the index with:

```coq
replace (k + 0) with k by lia.
```

before applying `H10`.

## 2026-04-23 proof iteration 7

The next compile failed in the return witness's nested cons case:

```text
File ".../string_copy_prefix_proof_manual.v", line 160, characters 8-131:
Error: No matching clauses for match.
```

This is the same syntactic fragility as iteration 4, now after destructing the final destination suffix tail. I will pose the current `Zlength (z :: d1) = ...` hypothesis as `Hlen_d1_cons`, rewrite `Zlength_cons` in that named hypothesis, and then reuse the same named fact after destructing the tail. This avoids matching on `1 + Zlength ...` directly.
