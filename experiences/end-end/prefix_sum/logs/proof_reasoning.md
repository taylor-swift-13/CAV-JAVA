## 2026-04-22 proof plan after successful symexec

Fresh `symexec` succeeded on the latest active annotated file and generated:

```text
coq/generated/prefix_sum_goal.v
coq/generated/prefix_sum_proof_auto.v
coq/generated/prefix_sum_proof_manual.v
coq/generated/prefix_sum_goal_check.v
```

`proof_auto.v` already covers:

```coq
Lemma proof_of_prefix_sum_safety_wit_1 : prefix_sum_safety_wit_1.
Lemma proof_of_prefix_sum_safety_wit_2 : prefix_sum_safety_wit_2.
Lemma proof_of_prefix_sum_safety_wit_4 : prefix_sum_safety_wit_4.
Lemma proof_of_prefix_sum_partial_solve_wit_1 : prefix_sum_partial_solve_wit_1.
Lemma proof_of_prefix_sum_partial_solve_wit_2 : prefix_sum_partial_solve_wit_2.
```

The manual file contains four admitted goals:

```coq
Lemma proof_of_prefix_sum_safety_wit_3 : prefix_sum_safety_wit_3.
Lemma proof_of_prefix_sum_entail_wit_1 : prefix_sum_entail_wit_1.
Lemma proof_of_prefix_sum_entail_wit_2 : prefix_sum_entail_wit_2.
Lemma proof_of_prefix_sum_return_wit_1 : prefix_sum_return_wit_1.
```

`prefix_sum_safety_wit_3` asks for the signed-int range of `acc + Znth i la 0`. The invariant gives `acc = sum(sublist 0 i la)`, and the precondition gives signed-int range for every `sum(sublist 0 k la)` with `0 <= k <= n_pre`. The missing bridge is the list arithmetic lemma:

```coq
sum (sublist 0 (i + 1) la) =
  sum (sublist 0 i la) + Znth i la 0
```

under `0 <= i < Zlength la`. This same shape appears in the verified `array_sum` proof as `sum_sublist_snoc`; I will add a local helper with a `prefix_sum_` prefix to avoid name collisions.

`prefix_sum_entail_wit_1` is invariant initialization. The witness should be `l1 = nil` and `l2 = lo`, so `app nil lo = lo`, `Zlength nil = 0`, and the value facts are either vacuous or direct.

`prefix_sum_entail_wit_2` is invariant preservation after writing `out[i]`. The proof pattern matches `array_scale_entail_wit_2`: first prove the old suffix `l2_2` equals `sublist i n_pre lo`, then choose:

```coq
l2 = sublist (i + 1) n_pre lo
l1 = l1_2 ++ cons (sum (sublist 0 (i + 1) la)) nil
```

The spatial target follows by normalizing `replace_Znth i ... (app l1_2 l2_2)` over the append boundary. The pure prefix facts split on whether `k < i` or `k = i`; the new final element uses the just-written value and the sum-snoc helper.

`prefix_sum_return_wit_1` is the completed loop exit. From `i_2 >= n_pre` and `i_2 <= n_pre`, `i_2 = n_pre`. Choosing `lr = app l1 l2` should let the spatial goal close immediately; for values, every postcondition index lies in the completed prefix, so `app_Znth1` and the invariant's prefix fact apply.

## 2026-04-22 first manual compile failure

Compiling after the first proof edit produced:

```text
compiled prefix_sum_goal.v
compiled prefix_sum_proof_auto.v
File ".../prefix_sum_proof_manual.v", line 78, characters 14-16:
Error:
...
Ht : 0 <= t < Zlength l2_2
The term "Ht" has type "0 <= t < Zlength l2_2"
while it is expected to have type "0 <= t < n_pre - Zlength l1_2".
```

This is not a semantic failure. I copied the `array_scale` suffix-reconstruction skeleton, but the generated hypothesis numbering differs in `prefix_sum_entail_wit_2`: `H5` is `Zlength l1_2 = i`, `H6` is `Zlength l2_2 = n_pre - i`, `H7` is the prefix value fact, and `H8` is the suffix value fact. The failed block was still rewriting with the wrong length hypothesis. The next edit changes the suffix reconstruction to rewrite `Ht` through `H6`, call `H8`, and use `H5`/`H7` everywhere the proof reasons about the prefix length/value facts.

## 2026-04-22 second manual compile failure

After fixing `entail_wit_2`, compilation reached `prefix_sum_return_wit_1` and failed at the per-index postcondition proof:

```text
File ".../prefix_sum_proof_manual.v", line 159, characters 10-12:
Error:
...
H7 :
  forall k_2 : Z,
  0 <= k_2 < Zlength l1 ->
  Znth k_2 l1 0 = sum (sublist 0 (k_2 + 1) la)
H6 : Zlength l2 = n_pre - Zlength l1
...
Unable to unify "Zlength l2 = n_pre - Zlength l1" with
 "Znth i l1 0 = sum (sublist 0 (i + 1) la)".
```

Again the proof shape is right but the copied hypothesis number is wrong. In this return witness, `H7` is the completed-prefix value fact and `H6` is only the suffix length fact. The next edit changes `apply H6` to `apply H7` in the return witness.

## 2026-04-22 manual proof completed

After changing the return witness to use `H7`, the full compile template succeeded:

```text
compiled prefix_sum_goal.v
compiled prefix_sum_proof_auto.v
compiled prefix_sum_proof_manual.v
compiled prefix_sum_goal_check.v
compile_end=2026-04-22T21:13:56+08:00
```

The final `proof_manual.v` contains the local helper:

```coq
Lemma prefix_sum_sum_sublist_snoc :
  forall (l : list Z) (i : Z),
    0 <= i < Zlength l ->
    sum (sublist 0 (i + 1) l) =
      sum (sublist 0 i l) + Znth i l 0.
```

This helper is used in `proof_of_prefix_sum_safety_wit_3` to connect the overflow precondition at `k = i + 1` with the C expression `acc + a[i]`, and in `proof_of_prefix_sum_entail_wit_2` to prove that the just-written value equals the semantic prefix sum for the new last prefix cell. The preservation proof reconstructs the output list as `l1_2 ++ [sum(sublist 0 (i + 1) la)] ++ sublist (i + 1) n_pre lo` and then closes the spatial goal with the normalized `app` shape.

Final manual proof checks:

```text
proof_manual.v contains Admitted.: no
proof_manual.v contains top-level Axiom: no
goal_check.v compiled: yes
```
