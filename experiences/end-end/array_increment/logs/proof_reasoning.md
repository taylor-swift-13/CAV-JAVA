## 2026-04-22 proof round 1: discharge overflow and replacement witness

After fresh `symexec`, `coq/generated/array_increment_proof_manual.v` contains two generated admitted obligations:

```coq
Lemma proof_of_array_increment_safety_wit_3 : array_increment_safety_wit_3.
Proof. Admitted.

Lemma proof_of_array_increment_which_implies_wit_2 : array_increment_which_implies_wit_2.
Proof. Admitted.
```

The first goal, `array_increment_safety_wit_3`, is the safety check for evaluating `a[i] + 1` after the bridge assertion has exposed:

```coq
IntArray.missing_i a_pre i 0 n_pre lr **
((a_pre + (i * sizeof(INT))) # Int |-> Znth i l 0)
```

The pure context includes `0 <= i`, `i < n_pre`, and the contract overflow guard:

```coq
forall i_2,
  0 <= i_2 /\ i_2 < n_pre ->
  INT_MIN <= Znth i_2 l 0 + 1 /\ Znth i_2 l 0 + 1 <= INT_MAX
```

Plan: `pre_process`, instantiate the overflow guard at `i`, then let `entailer!`/`lia` close the two pure bounds.

The second goal, `array_increment_which_implies_wit_2`, is the post-write bridge:

```coq
IntArray.missing_i a_pre i 0 n_pre lr **
((a_pre + (i * sizeof(INT))) # Int |-> Znth i l 0 + 1)
|-- EX lr', ... IntArray.full a_pre n_pre lr'
```

The natural witness is:

```coq
replace_Znth i (Znth i l 0 + 1) lr
```

This restores the focused cell with the incremented value while leaving all other positions unchanged. The prefix proof splits on `k = i`: for `k = i`, `Znth_replace_Znth_same` gives the new value; for `k < i`, `Znth_replace_Znth_diff` preserves `lr[k]`, then the old prefix invariant gives `lr[k] == l[k] + 1`. The suffix proof has `i + 1 <= k`, so `k <> i`; `Znth_replace_Znth_diff` preserves `lr[k]`, then the old suffix invariant gives `lr[k] == l[k]`. The heap part is closed by `IntArray.missing_i_merge_to_full`, and the length proof uses `Zlength_replace_Znth`.

I will add local helper lemmas for `Zlength_replace_Znth`, `Znth_replace_Znth_same`, and `Znth_replace_Znth_diff`, following the same pattern as the existing verified `array_clamp_nonnegative` proof.

## 2026-04-22 proof round 2: first compile failure in length side condition

Compile command: full `coqc` load path from `QualifiedCProgramming/SeparationLogic`, compiling `array_increment_goal.v`, `array_increment_proof_auto.v`, `array_increment_proof_manual.v`, and `array_increment_goal_check.v`.

First stable error:

```text
File ".../array_increment_proof_manual.v", line 103, characters 4-32:
Error: Found no subterm matching
"Zlength (replace_Znth ?M6061 ?M6062 ?M6063)" in the current goal.
```

This occurs in the first bullet after `entailer!` for `proof_of_array_increment_which_implies_wit_2`:

```coq
- rewrite Zlength_replace_Znth.
  lia.
```

The intended side condition is the witness length. In this proof state, `entailer!` has already simplified or oriented the length goal so that there is no syntactic `Zlength (replace_Znth ...)` occurrence left for `rewrite` to match. The fix is to make this bullet robust by trying the rewrite only if the matching subterm is present, then closing the remaining arithmetic/length equality with `lia`.

The above diagnosis was incomplete. A `coqtop` replay stopped immediately after:

```coq
pre_process.
Exists (replace_Znth i (Znth i l 0 + 1) lr).
entailer!.
Show.
```

The real subgoal order is:

```text
1. IntArray.missing_i ... ** data_at ... |-- IntArray.full ...
2. forall k_2, i + 1 <= k_2 < n_pre -> Znth k_2 (replace_Znth ...) 0 = Znth k_2 l 0
3. forall k, 0 <= k < i + 1 -> Znth k (replace_Znth ...) 0 = Znth k l 0 + 1
4. Zlength (replace_Znth i (Znth i l 0 + 1) lr) = n_pre
```

So the earlier script failed because the first bullet was trying to prove the heap-merging goal with the length proof. The next edit reorders bullets as heap, suffix, prefix, length. The heap bullet uses `IntArray.missing_i_merge_to_full` and `replace_Znth_Znth`; the pure bullets use the local `Znth_replace_Znth_*` lemmas and the invariant prefix/suffix hypotheses.

## 2026-04-22 proof round 3: heap merge does not need `replace_Znth_Znth`

After reordering bullets, the next compile stopped at the heap bullet:

```text
File ".../array_increment_proof_manual.v", line 104, characters 4-38:
Error: Found no subterm matching
"replace_Znth ?M6309 (Znth ?M6309 ?M6310 ?M6311) ?M6310" in the current goal.
```

The failing line was:

```coq
rewrite replace_Znth_Znth by tauto.
```

That rewrite is useful when the merged cell value is syntactically `Znth i lr 0`, so the replacement is a no-op. Here the merged cell value is intentionally `Znth i l 0 + 1`; the target array witness is exactly `replace_Znth i (Znth i l 0 + 1) lr`. Therefore `IntArray.missing_i_merge_to_full` should already produce the right heap assertion, and the no-op rewrite is not only unnecessary but inapplicable. The fix is to remove the rewrite and close with `entailer!`.
