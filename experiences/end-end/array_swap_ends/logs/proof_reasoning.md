## 2026-04-22 manual return witnesses after successful symexec

Current generated proof file: `output/verify_20260422_090412_array_swap_ends/coq/generated/array_swap_ends_proof_manual.v`.

The fresh `symexec` run succeeded on the active annotated file and generated `array_swap_ends_goal.v`, `array_swap_ends_proof_auto.v`, `array_swap_ends_proof_manual.v`, and `array_swap_ends_goal_check.v`. The manual file contains exactly two admitted lemmas:

```coq
Lemma proof_of_array_swap_ends_return_wit_1 : array_swap_ends_return_wit_1.
Proof. Admitted.

Lemma proof_of_array_swap_ends_return_wit_2 : array_swap_ends_return_wit_2.
Proof. Admitted.
```

`array_swap_ends_return_wit_1` is the `n_pre >= 2` path after executing:

```c
t = a[0];
a[0] = a[n - 1];
a[n - 1] = t;
```

The generated heap already owns:

```coq
IntArray.full a_pre n_pre
  (replace_Znth (n_pre - 1) (Znth 0 l 0)
    (replace_Znth 0 (Znth (n_pre - 1) l 0) l))
```

So the proof should choose that double-replacement list as `l0`. The remaining pure postcondition is pointwise: index `0` equals the old last element, index `n_pre - 1` equals the old first element, and all other indices are unchanged. This needs local helper facts for `Zlength (replace_Znth ...)`, reading the same replaced index, and reading a different replaced index. The proof must use `n_pre >= 2` to establish `0 <> n_pre - 1`.

`array_swap_ends_return_wit_2` is the early-return path with `n_pre < 2`. It should choose `l` as `l0`; the `n_pre < 2` implication is reflexive, and the `n_pre >= 2` implication is contradictory by arithmetic.

Planned edit: add local lemmas `array_swap_ends_Zlength_replace_Znth`, `array_swap_ends_Znth_replace_Znth_same`, and `array_swap_ends_Znth_replace_Znth_diff`, then replace the two `Admitted.` placeholders with explicit `pre_process`, `Exists`, `entailer!`, case split, rewrite, and `lia` proofs.

First compile result: the full compile replay reached `array_swap_ends_proof_manual.v` and failed before the witnesses:

```text
File ".../array_swap_ends_proof_manual.v", line 28, characters 10-28:
Error: The variable length_replace_nth was not found in the current environment.
```

The local length helper had copied a lemma name from another proof environment, but this generated file only imports the QCP `ListLib` definitions and not that particular length lemma. Next edit: make the proof self-contained by adding a small `array_swap_ends_replace_nth_length` lemma by induction on the list, then use it inside `array_swap_ends_Zlength_replace_Znth`. I will also add local nat-level same/different-index lemmas so the `Znth` helpers do not depend on environment-specific names.

Second compile result: after adding the self-contained helper lemmas, parsing failed at the helper proof line using `induction l as [| h t IH]`:

```text
File ".../array_swap_ends_proof_manual.v", line 27, characters 17-19:
Error: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

This is a syntax interaction in the generated proof environment, not a logical failure. Next edit: replace the explicit `as [| h t IH]` induction patterns with plain `induction l`, using Coq-generated names only inside the immediately following proof steps.

Third compile/probe result: after the helper syntax fix, `array_swap_ends_proof_manual.v` failed at the first bullet of `return_wit_1` because `entailer!` leaves the pointwise `forall i` obligation before the `Zlength` obligation:

```coq
(* first remaining goal *)
forall i : Z,
  0 <= i < n_pre ->
  (n_pre < 2 -> ...) /\ (n_pre >= 2 -> ...)

(* second remaining goal *)
Zlength (replace_Znth (n_pre - 1) ... (replace_Znth 0 ... l)) = n_pre
```

The original bullets handled length first. Next edit: reorder the bullets so the pointwise proof is first and the length proof is second.

Fourth compile result: after reordering `return_wit_1`, compilation reached `return_wit_2` and failed with:

```text
File ".../array_swap_ends_proof_manual.v", line 142, characters 2-14:
Error: No such goal.
```

This means `pre_process; Exists l; entailer!` already proves the early-return postcondition from `n_pre < 2`, `0 <= n_pre`, and `Zlength l = n_pre`; the extra manual `intros i Hi` block was stale. Next edit: reduce `return_wit_2` to the minimal three-command proof.
