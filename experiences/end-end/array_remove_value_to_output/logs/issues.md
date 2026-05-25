## 2026-04-22 07:12 +0800 - Fingerprint placeholder filled

- Phenomenon: `logs/workspace_fingerprint.json` was still the script-initialized placeholder with an empty `semantic_description` and `{}` keywords.
- Trigger: Verify workflow requires the fingerprint to be useful for later retrieval early in the task, and keyword keys/values must come only from `doc/retrieval/INDEX.md`.
- Location: `logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a semantic description for the array scan/copy-filter loop and used only controlled vocabulary values:

```json
"keywords": {
  "algorithm_family": "selection",
  "control_flow": "while_loop",
  "data_shape": ["array", "pointer"],
  "semantic_intent": ["preserve_input", "in_place_update"],
  "proof_pattern": ["loop_invariant", "case_split", "heap_reasoning", "range_bound"],
  "edge_case_behavior": "empty_loop_possible"
}
```

- Result: the fingerprint is nonempty and, after final verification, records `verification_status: ["goal_check_passed", "proof_check_passed"]`.

## 2026-04-22 07:13 +0800 - Missing loop invariant for output-prefix filtering

- Phenomenon: the active annotated C initially had a `while (i < n)` loop with no `Inv`, so there was no durable relation between `write`, the processed prefix of `la`, and the already written prefix of `out`.
- Trigger: the postcondition requires `__return == Zlength(array_remove_value_to_output_spec(la, k@pre))` and an output heap shaped as `app(array_remove_value_to_output_spec(la, k@pre), tail)`. Without an invariant, the loop body can execute symbolically, but the return witness would have no prefix-filter fact to use.
- Location: `annotated/verify_20260422_071205_array_remove_value_to_output.c`, loop before `while (i < n)`.
- Fix action: added an invariant with existential `lout`:

```c
/*@ Inv exists lout,
      0 <= i && i <= n@pre &&
      0 <= write && write <= i &&
      n == n@pre &&
      a == a@pre &&
      out == out@pre &&
      k == k@pre &&
      n@pre == Zlength(la) &&
      n@pre == Zlength(lo) &&
      Zlength(lout) == n@pre &&
      write == Zlength(array_remove_value_to_output_spec(sublist(0, i, la), k@pre)) &&
      (forall (p: Z),
        (0 <= p && p < write) =>
        lout[p] == array_remove_value_to_output_spec(sublist(0, i, la), k@pre)[p]) &&
      (forall (p: Z),
        (write <= p && p < n@pre) =>
        lout[p] == lo[p]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, lout)
*/
```

Also added a loop-exit assertion that fixes `i == n@pre`, rewrites the processed prefix to the full `la`, and preserves the same `lout` prefix/suffix facts for the return witness.

- Result: rerunning `symexec` succeeded and generated fresh `array_remove_value_to_output_goal.v`, `array_remove_value_to_output_proof_auto.v`, `array_remove_value_to_output_proof_manual.v`, and `array_remove_value_to_output_goal_check.v`.

## 2026-04-22 07:14 +0800 - Fresh symbolic execution

- Phenomenon: after editing `Inv`/`Assert`, old generated Coq files could not be trusted.
- Trigger: verify workflow requires clearing generated files and rerunning `symexec` after every annotation change.
- Command:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --goal-file=output/verify_20260422_071205_array_remove_value_to_output/coq/generated/array_remove_value_to_output_goal.v \
  --proof-auto-file=output/verify_20260422_071205_array_remove_value_to_output/coq/generated/array_remove_value_to_output_proof_auto.v \
  --proof-manual-file=output/verify_20260422_071205_array_remove_value_to_output/coq/generated/array_remove_value_to_output_proof_manual.v \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_071205_array_remove_value_to_output \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --input-file=annotated/verify_20260422_071205_array_remove_value_to_output.c \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ended with:

```text
Successfully finished symbolic execution
symexec_end=2026-04-22 07:14:20 +0800
symexec_status=0
```

## 2026-04-22 07:15 +0800 - Manual list witnesses required

- Phenomenon: generated `coq/generated/array_remove_value_to_output_proof_manual.v` contained five admitted obligations:

```coq
proof_of_array_remove_value_to_output_entail_wit_1
proof_of_array_remove_value_to_output_entail_wit_2_1
proof_of_array_remove_value_to_output_entail_wit_2_2
proof_of_array_remove_value_to_output_entail_wit_3
proof_of_array_remove_value_to_output_return_wit_1
```

- Trigger: `symexec` can generate the VCs, but the filtered-prefix preservation and final prefix/suffix reconstruction are pure list facts not solved automatically.
- Location: `coq/generated/array_remove_value_to_output_proof_manual.v`.
- Fix action: added local helper lemmas for `replace_Znth` length/same/other, filter snoc keep/drop, filter length bounds, and prefix-tail rebuilding:

```coq
Lemma arvo_spec_snoc_keep :
  forall xs x k,
    x <> k ->
    array_remove_value_to_output_spec (xs ++ [x]) k =
    array_remove_value_to_output_spec xs k ++ [x].

Lemma arvo_spec_snoc_drop :
  forall xs x k,
    x = k ->
    array_remove_value_to_output_spec (xs ++ [x]) k =
    array_remove_value_to_output_spec xs k.

Lemma arvo_prefix_tail_rebuild :
  forall (spec lout: list Z) n write,
    Zlength lout = n ->
    Zlength spec = write ->
    0 <= write <= n ->
    (forall p, 0 <= p /\ p < write -> Znth p lout 0 = Znth p spec 0) ->
    lout = spec ++ sublist write n lout.
```

- Result: all five manual witnesses were completed without `Admitted.` or new `Axiom`.

## 2026-04-22 07:17 +0800 - `entailer!` goal order differed by witness

- Phenomenon: the first proof script for `entail_wit_2_1` failed with rewrite and bullet-order errors. One representative error was:

```text
File ".../array_remove_value_to_output_proof_manual.v", line 187:
Error: Found no subterm matching
"array_remove_value_to_output_spec (sublist 0 (i + 1) la) k_pre"
in the current goal.
```

Then, after changing the rewrite direction without checking goal order, Coq reported:

```text
Error: No such goal. Focus next goal with bullet +.
```

- Trigger: after `entailer!`, `entail_wit_2_1` produced suffix preservation first, then prefix preservation, then filtered-length equality, then `replace_Znth` length. `entail_wit_2_2` produced only prefix preservation and filtered-length equality; the unchanged suffix was solved automatically.
- Location: `proof_of_array_remove_value_to_output_entail_wit_2_1` and `proof_of_array_remove_value_to_output_entail_wit_2_2`.
- Fix action: used `coqtop` to inspect the live goal order. Reordered the bullets in `entail_wit_2_1`:

```coq
entailer!.
- intros p Hp. (* suffix *)
  rewrite arvo_Znth_replace_Znth_other; try lia.
  apply H10; lia.
- intros p Hp. (* prefix *)
  rewrite Hspec_next.
  ...
- rewrite Hspec_next. (* length *)
  ...
- rewrite arvo_replace_Znth_length.
  exact H7.
```

For `entail_wit_2_2`, kept only the two goals that remained after `entailer!`.

- Result: `array_remove_value_to_output_proof_manual.v` compiled successfully.

## 2026-04-22 07:20 +0800 - Full compile and cleanup

- Phenomenon: successful `symexec` and manual proof compilation are not enough; verify completion requires compiling the original task Coq file, `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, then deleting generated intermediates.
- Trigger: workflow completion standard.
- Command shape: used the stable compile template from `experiences/general/COMPILE.md` with `-Q "$ORIG" ""` for `original/array_remove_value_to_output.v` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_071205_array_remove_value_to_output` for generated files.
- Result: `logs/compile_all.log` contains:

```text
compiled=array_remove_value_to_output.v
compiled=array_remove_value_to_output_goal.v
compiled=array_remove_value_to_output_proof_auto.v
compiled=array_remove_value_to_output_proof_manual.v
compiled=array_remove_value_to_output_goal_check.v
```

`rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/array_remove_value_to_output_proof_manual.v` returned no matches. After `find coq -type f ! -name '*.v' -delete`, a follow-up `find coq -type f ! -name '*.v'` returned no files. The temporary `.vo/.glob/.vos/.vok/.aux` files created next to `original/array_remove_value_to_output.v` by compiling the task-specific Coq import were also removed.
