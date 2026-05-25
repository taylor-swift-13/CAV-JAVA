## Fingerprint placeholders had to be replaced early

- Phenomenon: the initialized workspace fingerprint had an empty `semantic_description` and empty `keywords`:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: Verify workflow requires the fingerprint to be made useful early, and `keywords` must use only the controlled vocabulary from `doc/retrieval/INDEX.md`.
- Localization: `output/verify_20260422_045751_array_increment/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a semantic description for the in-place array increment loop and used only controlled keys/values such as `for_loop`, `array`, `pointer`, `in_place_update`, `loop_invariant`, `heap_reasoning`, `overflow_guard`, and `empty_loop_possible`. After final verification, added `verification_status: ["goal_check_passed", "proof_check_passed"]`.
- Result: the fingerprint is non-empty and uses only the controlled vocabulary.

## The array update loop needed a prefix/suffix invariant

- Phenomenon: the active annotated C initially matched the input C and had no loop invariant around:

```c
for (i = 0; i < n; ++i) {
    a[i] = a[i] + 1;
}
```

- Trigger: symbolic execution needs a loop-head summary that states which prefix has already been incremented and which suffix remains unchanged. Without that, the postcondition existential `lr` cannot be connected to the mutated heap.
- Localization: `annotated/verify_20260422_045751_array_increment.c`, immediately before and inside the `for` loop.
- Fix action: added an invariant with witness `lr`:

```c
/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lr) == n@pre &&
      (forall (k: Z), (0 <= k && k < i) => lr[k] == l[k] + 1) &&
      (forall (k: Z), (i <= k && k < n@pre) => lr[k] == l[k]) &&
      IntArray::full(a, n@pre, lr)
*/
```

Then added a pre-write bridge that exposes the focused cell as `data_at(..., l[i])` and a post-write bridge that restores `IntArray::full` with a fresh `lr'` whose prefix through `i` has been incremented.

- Result: `QualifiedCProgramming/linux-binary/symexec` succeeded on the latest annotated file. `logs/qcp_run.log` ends with:

```text
End of symbolic execution of function array_increment
Successfully finished symbolic execution
symexec_status=0
```

## Manual proof obligations remained after symexec

- Phenomenon: fresh `symexec` generated `array_increment_proof_manual.v` with two admitted obligations:

```coq
Lemma proof_of_array_increment_safety_wit_3 : array_increment_safety_wit_3.
Proof. Admitted.

Lemma proof_of_array_increment_which_implies_wit_2 : array_increment_which_implies_wit_2.
Proof. Admitted.
```

- Trigger: `safety_wit_3` needed the contract overflow guard instantiated at the current loop index `i`; `which_implies_wit_2` needed a concrete array witness after writing one cell.
- Localization: `output/verify_20260422_045751_array_increment/coq/generated/array_increment_proof_manual.v`.
- Fix action: proved `safety_wit_3` with `pre_process`, the overflow hypothesis at `i`, and `entailer!`. Proved `which_implies_wit_2` using the witness:

```coq
replace_Znth i (Znth i l 0 + 1) lr
```

and local helper lemmas for `Zlength_replace_Znth`, `Znth_replace_Znth_same`, and `Znth_replace_Znth_diff`.

- Result: `array_increment_proof_manual.v` compiles and contains no `Admitted.` and no local top-level `Axiom`.

## Proof bullet order after `entailer!` was heap-first, not length-first

- Phenomenon: the first manual proof script for `which_implies_wit_2` failed with:

```text
Error: Found no subterm matching
"Zlength (replace_Znth ?M6061 ?M6062 ?M6063)" in the current goal.
```

Then after making the rewrite optional, it failed with:

```text
Error: Tactic failure: Cannot find witness.
```

- Trigger: after:

```coq
pre_process.
Exists (replace_Znth i (Znth i l 0 + 1) lr).
entailer!.
```

the generated subgoal order was heap, suffix property, prefix property, and only then length. The script had been written as length, prefix, suffix, heap.
- Localization: `array_increment_proof_manual.v`, `proof_of_array_increment_which_implies_wit_2`.
- Fix action: used `coqtop` and `Show` to inspect the actual subgoal order, then reordered bullets:

```coq
- sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
  entailer!.
- intros k Hk. ... suffix proof ...
- intros k Hk. ... prefix proof ...
- rewrite Zlength_replace_Znth. lia.
```

- Result: the reordered proof compiled through `array_increment_goal_check.v`.

## Heap merge did not need a no-op replacement rewrite

- Phenomenon: after reordering bullets, the heap bullet failed with:

```text
Error: Found no subterm matching
"replace_Znth ?M6309 (Znth ?M6309 ?M6310 ?M6311) ?M6310" in the current goal.
```

- Trigger: the script copied a common no-op rewrite pattern:

```coq
rewrite replace_Znth_Znth by tauto.
```

That rewrite applies when the replacement value is the list's existing `Znth` value. Here the replacement value is intentionally `Znth i l 0 + 1`, and the witness is exactly `replace_Znth i (Znth i l 0 + 1) lr`, so no no-op rewrite is appropriate.
- Localization: `array_increment_proof_manual.v`, heap bullet of `proof_of_array_increment_which_implies_wit_2`.
- Fix action: removed the `replace_Znth_Znth` rewrite and let:

```coq
sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
entailer!.
```

close the heap assertion.
- Result: final full compile succeeded:

```text
compiled=array_increment_goal.v
compiled=array_increment_proof_auto.v
compiled=array_increment_proof_manual.v
compiled=array_increment_goal_check.v
compile_status=0
```

## Final cleanup was required after successful compile

- Phenomenon: successful Coq compilation left generated `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under `coq/generated/`.
- Trigger: Verify completion requires cleaning non-`.v` Coq intermediates after the successful compile pass.
- Localization: `output/verify_20260422_045751_array_increment/coq/generated/`.
- Fix action: deleted all files under the workspace `coq/` directory whose names do not end in `.v`.
- Result: `find output/verify_20260422_045751_array_increment/coq -type f ! -name '*.v'` prints no files.
