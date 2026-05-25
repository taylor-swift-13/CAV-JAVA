# Verify Issues

## Fingerprint placeholder had to be filled before verification

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and empty `keywords`.
- Trigger: the verify workflow requires the fingerprint to be populated early, and the user explicitly required reading `doc/retrieval/INDEX.md` first so all keyword keys and values come from its controlled vocabulary.
- Location: `output/verify_20260422_030111_array_count_distinct_sorted/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled the semantic description with the behavior of the read-only sorted-array distinct-run scan.  Used controlled keywords including `algorithm_family: counting`, `control_flow: [if, while_loop]`, `data_shape: array`, `semantic_intent: preserve_input`, and proof patterns `loop_invariant`, `case_split`, `range_bound`, and `heap_reasoning`.  After final compile success, added `verification_status: [goal_check_passed, proof_check_passed]`.
- Result: the fingerprint no longer contains empty placeholders and uses only controlled vocabulary.

## Loop needed an invariant over the processed prefix

- Phenomenon: the input C file had a `while (i < n)` loop but no `Inv`, so symbolic execution could not preserve the relationship between `count` and the prefix already scanned.
- Trigger: the loop updates `count` only when `a[i] != a[i - 1]`; the postcondition needs `count == array_count_distinct_sorted_spec(l)` at return, so the invariant must describe the prefix `sublist(0, i, l)`.
- Location: active annotated file `annotated/verify_20260422_030111_array_count_distinct_sorted.c`, immediately before `while (i < n)`.
- Fix action: appended detailed reasoning to `logs/annotation_reasoning.md`, then added:

```c
/*@ Inv
      1 <= i && i <= n &&
      1 <= count && count <= i &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_distinct_sorted_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

- Result: `symexec` succeeded on the updated annotated file and generated fresh `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## Manual witnesses reduced to pure prefix/list facts

- Phenomenon: generated `coq/generated/array_count_distinct_sorted_proof_manual.v` contained five `Admitted.` placeholders:

```coq
proof_of_array_count_distinct_sorted_entail_wit_1
proof_of_array_count_distinct_sorted_entail_wit_2_1
proof_of_array_count_distinct_sorted_entail_wit_2_2
proof_of_array_count_distinct_sorted_return_wit_1
proof_of_array_count_distinct_sorted_return_wit_2
```

- Trigger: after `pre_process; entailer!`, the remaining goals were pure Coq facts such as `1 = array_count_distinct_sorted_spec (sublist 0 1 l)`, loop-step equalities for `sublist 0 (i_2 + 1) l`, and return normalization from `sublist 0 n_pre l` to `l`.
- Location: `output/verify_20260422_030111_array_count_distinct_sorted/coq/generated/array_count_distinct_sorted_proof_manual.v`.
- Fix action: added local helper lemmas for prefix snoc decomposition, last element of a prefix, distinct-count snoc over a nonempty list, and nonempty prefixes.  The witness proofs then rewrite by these helpers and use the branch equality/disequality with `lia`.
- Result: all five manual witness lemmas compile with `Qed`; `proof_manual.v` contains no `Admitted.` and no top-level `Axiom`.

## `sac` scope made list bracket notation parse as assertions

- Phenomenon: the first manual proof compile failed with:

```text
The term "[Znth i l 0]" has type "Z -> Prop"
while it is expected to have type "list Z".
```

- Trigger: generated proof files open `Local Open Scope sac`; in that scope, bracket notation such as `[x]` and `[]` is not reliable for Coq lists.
- Location: helper lemmas initially added near the top of `array_count_distinct_sorted_proof_manual.v`.
- Fix action: replaced list bracket notation with explicit constructors:

```coq
Znth i l 0 :: nil
xs <> nil
```

- Result: the notation error disappeared, and the helper lemmas compiled.

## Compile replay must be fail-fast

- Phenomenon: an early compile shell block continued after a `coqc` failure and printed misleading `compiled ...` lines for later files.
- Trigger: the commands were grouped and piped through `tee` without `set -e`, so the group kept running after `proof_manual.v` failed.
- Location: `logs/compile.log` was overwritten by the later successful fail-fast replay, but the failed error chain was observed during proof repair.
- Fix action: reran the compile template with `set -euo pipefail` so the first failing `coqc` stops the replay.
- Result: the final `logs/compile.log` contains only the successful fail-fast replay through `array_count_distinct_sorted_goal_check.v`.

## Final Coq artifact cleanup

- Phenomenon: Coq compilation generated `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under `coq/generated/`.
- Trigger: normal `coqc` compilation leaves build artifacts, but verify completion requires `coq/` to contain only `.v` source files.
- Location: `output/verify_20260422_030111_array_count_distinct_sorted/coq/generated/`.
- Fix action: ran `find "$WS/coq" -type f ! -name '*.v' -delete`, then checked that `find "$WS/coq" -type f ! -name '*.v' -print` produced no output.
- Result: non-`.v` Coq intermediates were removed.
