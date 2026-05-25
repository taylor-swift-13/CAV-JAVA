## 2026-04-22T13:49:37+08:00 - Workspace fingerprint initially had empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` had `"semantic_description": ""` and `"keywords": {}` at task start.
- Trigger: the verify workflow requires reading `doc/retrieval/INDEX.md` early and then replacing the placeholder fingerprint fields with non-empty semantic content using only the controlled vocabulary.
- Location: `output/verify_20260422_133747_copy_array/logs/workspace_fingerprint.json`.
- Fix: read `doc/retrieval/INDEX.md` and filled `semantic_description` with the copy semantics, source preservation, destination mutation, single `for` loop, and empty-loop behavior. The `keywords` now use only controlled keys and values, including `algorithm_family: identity`, `control_flow: for_loop`, `data_shape: [array, pointer]`, `proof_pattern: [loop_invariant, heap_reasoning]`, and after success `verification_status: [goal_check_passed, proof_check_passed]`.
- Result: the fingerprint is non-empty and describes this workspace sufficiently for later retrieval.

## 2026-04-22T13:49:37+08:00 - Unannotated loop needed destination prefix/suffix invariant

- Phenomenon: the input and initial active annotated C file had a bare loop:

```c
for (i = 0; i < n; ++i) {
    dst[i] = src[i];
}
```

- Trigger: the postcondition requires `IntArray::full(dst, n, ls)`, but without an invariant there is no loop-head description of which destination cells already equal `ls` and which cells still equal the original `ld`.
- Location: `annotated/verify_20260422_133747_copy_array.c`.
- Fix: added an invariant with `exists l1 l2`, where `l1` is the copied prefix and `l2` is the original untouched suffix:

```c
Zlength(l1) == i &&
Zlength(l2) == n@pre - i &&
(forall (k: Z), (0 <= k && k < i) => l1[k] == ls[k]) &&
(forall (k: Z), (0 <= k && k < n@pre - i) => l2[k] == ld[i + k]) &&
IntArray::full(src, n@pre, ls) *
IntArray::full(dst, n@pre, app(l1, l2))
```

- Fix details: added a pre-assignment bridge opening `src[i]` and `dst[i]` with `IntArray::missing_i`, and a post-assignment bridge folding the updated destination into `app(l1', sublist(i + 1, n@pre, ld))`.
- Result: `QualifiedCProgramming/linux-binary/symexec` completed successfully on the current annotated file and generated `copy_array_goal.v`, `copy_array_proof_auto.v`, `copy_array_proof_manual.v`, and `copy_array_goal_check.v`.

## 2026-04-22T13:49:37+08:00 - Manual proof placeholders generated after successful symexec

- Phenomenon: `coq/generated/copy_array_proof_manual.v` initially contained five `Admitted.` placeholders:

```coq
Lemma proof_of_copy_array_entail_wit_1 : copy_array_entail_wit_1.
Lemma proof_of_copy_array_entail_wit_2 : copy_array_entail_wit_2.
Lemma proof_of_copy_array_return_wit_1 : copy_array_return_wit_1.
Lemma proof_of_copy_array_which_implies_wit_1 : copy_array_which_implies_wit_1.
Lemma proof_of_copy_array_which_implies_wit_2 : copy_array_which_implies_wit_2.
```

- Trigger: the generated VCs contained list-shape obligations for invariant initialization, loop preservation, return-list equality, and the two annotation `which implies` bridges.
- Location: `output/verify_20260422_133747_copy_array/coq/generated/copy_array_proof_manual.v`.
- Fix: filled all five proofs. The proof uses explicit invariant witnesses (`ld`, `nil`, `sublist (i + 1) n_pre ld`, `l1'`), `IntArray.full_split_to_missing_i` for cell access, `IntArray.missing_i_merge_to_full` for folding written cells, and list equalities via `list_eq_ext`, `Znth_sublist`, `sublist_split`, `sublist_single`, `replace_Znth_app_r`, and prefix/suffix facts.
- Result: `copy_array_proof_manual.v` compiles and contains no `Admitted.` and no new `Axiom` declaration.

## 2026-04-22T13:49:37+08:00 - Proof skeleton copied unstable generated hypothesis names

- Phenomenon: the first manual proof compile failed with:

```text
File ".../copy_array_proof_manual.v", line 32, characters 2-37:
Error: The variable i_2 was not found in the current environment.
```

- Trigger: the first proof attempt reused a nearby `array_add` proof skeleton. That example's `pre_process` named the loop index `i_2`, while this generated `copy_array` theorem uses `i`.
- Fix: changed `Exists (sublist (i_2 + 1) n_pre ld)` to `Exists (sublist (i + 1) n_pre ld)` and changed the return proof's copied `i_3` to local `i`.
- Result: compilation advanced past `entail_wit_2` to the return witness.

## 2026-04-22T13:49:37+08:00 - Return witness list equality direction was reversed

- Phenomenon: compilation then failed with:

```text
Error:
Unable to unify "l1 ++ l2 = ls" with "ls = l1 ++ l2".
```

- Trigger: after `replace (app l1 l2) with ls`, Coq generated the side condition in the direction `ls = app l1 l2`, while the copied extensional equality instantiated `list_eq_ext` as `(app l1 l2) ls`.
- Fix: instantiated `list_eq_ext` as `list_eq_ext 0 ls (app l1 l2)`, rewrote the right-hand side with `app_Znth1`, and used the copied-prefix fact symmetrically:

```coq
rewrite app_Znth1 by lia.
symmetry.
apply H6.
lia.
```

- Result: compilation advanced to `which_implies_wit_2`.

## 2026-04-22T13:49:37+08:00 - `which_implies_wit_2` needed stable names for invariant facts

- Phenomenon: subsequent proof compiles failed because copied hypothesis numbers did not mean the same facts in this generated context:

```text
Error: Found no subterm matching "Znth ?M6073 ls 0" in the current goal.
Error: The variable H7 was not found in the current environment.
Error: Found no subterm matching "Zlength (sublist i n_pre ld)" in the current goal.
```

- Trigger: the proof used numbered hypotheses such as `H4`, `H5`, `H6`, and `H7` from a similar example. In `copy_array`, `pre_process` produced different names and sometimes normalized `i` through `Zlength l1`, so the copied numbers were unstable.
- Fix: at the start of `proof_of_copy_array_which_implies_wit_2`, explicitly named the three invariant facts needed later:

```coq
assert (Hlen_l1 : Zlength l1 = i) by lia.
assert (Hprefix_all :
  forall k : Z, 0 <= k < i -> Znth k l1 0 = Znth k ls 0).
assert (Hsuffix_all :
  forall k : Z, 0 <= k < n_pre - i -> Znth k l2 0 = Znth (i + k) ld 0).
```

- Fix details: used these named facts instead of generated hypothesis numbers when proving `l2 = sublist i n_pre ld`, normalizing `replace_Znth_app_r`, preserving the prefix, and proving the final `l1 ++ [Znth i ls 0]` prefix semantics.
- Result: `copy_array_proof_manual.v` compiled successfully, then the full chain `copy_array_goal.v`, `copy_array_proof_auto.v`, `copy_array_proof_manual.v`, and `copy_array_goal_check.v` compiled successfully with empty compile logs.

## 2026-04-22T13:49:37+08:00 - Final cleanup removed Coq intermediate files

- Phenomenon: successful Coq compilation produced non-source intermediate files under `coq/generated/`, including `.aux`, `.glob`, `.vo`, `.vok`, and `.vos`.
- Trigger: the verify workflow requires cleaning `coq/` non-`.v` artifacts after successful compilation.
- Fix: ran `find coq -type f ! -name '*.v' -delete` in the workspace. Also checked `./input` for non-`.c` and non-`.v` files; none were present.
- Result: `coq/` now contains only:

```text
coq/generated/copy_array_goal.v
coq/generated/copy_array_goal_check.v
coq/generated/copy_array_proof_auto.v
coq/generated/copy_array_proof_manual.v
```

Final verification status:

- `symexec`: succeeded on the latest active annotated C file.
- `goal.v`: compiled successfully.
- `proof_auto.v`: compiled successfully.
- `proof_manual.v`: compiled successfully and contains no `Admitted.` or new `Axiom`.
- `goal_check.v`: compiled successfully.
- Cleanup: completed for workspace `coq/` intermediate files; no input intermediates were present.
