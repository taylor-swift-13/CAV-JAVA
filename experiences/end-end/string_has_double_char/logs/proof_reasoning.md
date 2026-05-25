
## Iteration 1 - manual witnesses after successful symexec

Fresh `symexec` succeeded after the annotated-only function rename workaround and generated five manual obligations in `coq/generated/string_has_double_char_proof_manual.v`:

```coq
Lemma proof_of_string_has_dup_char_entail_wit_1 : string_has_dup_char_entail_wit_1.
Lemma proof_of_string_has_dup_char_entail_wit_2 : string_has_dup_char_entail_wit_2.
Lemma proof_of_string_has_dup_char_entail_wit_3 : string_has_dup_char_entail_wit_3.
Lemma proof_of_string_has_dup_char_return_wit_1 : string_has_dup_char_return_wit_1.
Lemma proof_of_string_has_dup_char_return_wit_2 : string_has_dup_char_return_wit_2.
```

Current VC shapes:

- `entail_wit_1`: after the `s[0] != 0` branch, prove the initial loop invariant with `i = 1`, especially `1 <= n`. This follows from `Znth 0 (l ++ [0]) <> 0`, `Zlength l = n`, and the precondition that all positions `< n` in `l` are nonzero; if `n = 0`, the appended terminator is at index 0, contradiction.
- `entail_wit_2`: loop preservation after seeing `s[i] != 0`, checking `s[i] != s[i-1]`, and incrementing `i`. The key facts are `i < n` from nonzero at `l ++ [0]` and the adjacent inequality at the current index. The extended universal property splits on `j < i` vs `j = i`.
- `entail_wit_3`: loop exit assertion after `s[i] == 0`. The key bridge is `i = n`, again from the no-internal-zero string precondition and the terminator at `n`.
- `return_wit_1`: early return 0 from `s[0] == 0`; once `n = 0`, the universal postcondition over `1 <= i < n` is vacuous.
- `return_wit_2`: return 1 after finding equal adjacent chars. Use assertion-level `Right` and `Exists i_3`; prove `i_3 < n` from the nonzero read and rewrite `Znth` over `l ++ [0]` back to `l` for in-range indices.

The first proof attempt will use `pre_process`, assertion-level `Left`/`Right`/`Exists`, `entailer!`, and local list facts around `Znth_app1`/`Znth_app2`. No annotation change is planned unless a VC lacks the string no-internal-zero facts needed for these bridges.

## Iteration 2 - remove fragile generated hypothesis names

The first `coqc` run failed in `proof_manual.v` because the proof used `unfold ...; intros` and then referred to hypothesis `H`, but the assertion entailment was still a single separation-logic entailment at that point, so there was no pure hypothesis named `H`:

```text
File ".../string_has_double_char_proof_manual.v", line 31, characters 27-28:
Error: No such hypothesis: H
```

Fix: changed each manual lemma to start with `pre_process`, which extracts pure assumptions from the left side of the entailment into stable Coq hypotheses. A later compile found one remaining fragile numbered hypothesis in `entail_wit_3`:

```text
Error: The variable H6 was not found in the current environment.
```

Fix: replaced direct uses like `apply H6` and `apply H3` with a `match goal` that selects the semantic assumption by shape:

```coq
match goal with
| Hnz_all : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
    apply Hnz_all; lia
end.
```

Two proofs also had redundant `intros ...; lia` after `entailer!`; `entailer!` had already discharged those universal pure goals, causing `Error: No such goal.` Removing the redundant lines made `proof_manual.v` compile.

Final proof structure:

- `entail_wit_1`: `pre_process`, prove `1 <= n` by contradiction using the terminator at `Znth 0 (l ++ [0])`, then `entailer!`.
- `entail_wit_2`: prove `i < n` from `Znth i (l ++ [0]) <> 0`, split the extended processed-pair property on `j < i` vs `j = i`, then rewrite `app_Znth1` for the current adjacent pair.
- `entail_wit_3`: prove `i = n` from `Znth i (l ++ [0]) = 0` and no internal zero, then `subst` and `entailer!`.
- `return_wit_1`: prove `n = 0` from `Znth 0 (l ++ [0]) = 0`, choose assertion-level `Left`, and close with `entailer!`.
- `return_wit_2`: prove `i_3 < n`, choose assertion-level `Right`, provide `Exists i_3`, rewrite both appended-list reads to `l`, and close with the branch equality.

After these fixes, the full compile sequence for `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` completed successfully.
