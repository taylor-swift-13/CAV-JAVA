## Issue 1: Missing loop invariant in initial annotated copy

Symptom: the active annotated C file initially matched the input C and had no `Inv` or loop-exit `Assert` around:

```c
for (i = 0; i < n; ++i) {
    if (i % 2 == 0) {
        sum += a[i];
    }
}

return sum;
```

Without a loop invariant, symexec would not have a stable prefix relation for `sum` and would not retain the read-only array ownership needed by the final postcondition:

```c
__return == array_sum_even_indices_spec(l) &&
IntArray::full(a, n, l)
```

Fix: before modifying the annotated file, I wrote `logs/annotation_reasoning.md` and then added a prefix invariant at the actual `for` control point:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      sum == array_sum_even_indices_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
for (i = 0; i < n; ++i) { ... }
```

I also added a loop-exit assertion directly after the loop:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      sum == array_sum_even_indices_spec(l) &&
      IntArray::full(a, n, l)
*/
return sum;
```

Result: with this annotation, symexec completed successfully and generated `array_sum_even_indices_goal.v`, `array_sum_even_indices_proof_auto.v`, `array_sum_even_indices_proof_manual.v`, and `array_sum_even_indices_goal_check.v`.

## Issue 2: First symexec run used the wrong generated Coq logical path

Symptom: the first successful symexec run generated files whose imports used the generic path:

```coq
From SimpleC.EE Require Import array_sum_even_indices_goal.
```

and:

```coq
From SimpleC.EE Require Import array_sum_even_indices_goal array_sum_even_indices_proof_auto array_sum_even_indices_proof_manual.
```

This does not match the current CAV compile template, which compiles the current workspace's generated files under:

```text
SimpleC.EE.CAV.verify_20260422_085356_array_sum_even_indices
```

Trigger: I had run `symexec` with:

```bash
--coq-logic-path=SimpleC.EE
```

Fix: I deleted the generated files and reran symexec with the workspace-specific logical path:

```bash
LP=SimpleC.EE.CAV.verify_20260422_085356_array_sum_even_indices
QualifiedCProgramming/linux-binary/symexec \
  --goal-file="$GEN/array_sum_even_indices_goal.v" \
  --proof-auto-file="$GEN/array_sum_even_indices_proof_auto.v" \
  --proof-manual-file="$GEN/array_sum_even_indices_proof_manual.v" \
  --goal-check-file="$GEN/array_sum_even_indices_goal_check.v" \
  --coq-logic-path="$LP" \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --input-file=annotated/verify_20260422_085356_array_sum_even_indices.c \
  --no-exec-info
```

Result: the regenerated files import the current workspace prefix correctly:

```coq
From SimpleC.EE.CAV.verify_20260422_085356_array_sum_even_indices
  Require Import array_sum_even_indices_goal.
```

and `goal_check.v` imports goal, auto proof, and manual proof from the same workspace-specific prefix.

## Issue 3: Manual proof required prefix-extension lemmas for the even-index recursive spec

Symptom: after symexec, `array_sum_even_indices_proof_manual.v` contained five admitted manual obligations:

```coq
proof_of_array_sum_even_indices_safety_wit_6
proof_of_array_sum_even_indices_entail_wit_1
proof_of_array_sum_even_indices_entail_wit_2_1
proof_of_array_sum_even_indices_entail_wit_2_2
proof_of_array_sum_even_indices_entail_wit_3
```

The hard goals were pure list/arithmetic goals. For the even branch, the overflow witness needed to derive:

```coq
INT_MIN <= sum + Znth i l 0 /\
sum + Znth i l 0 <= INT_MAX
```

from the contract's prefix bound at `k = i + 1`, after rewriting:

```coq
array_sum_even_indices_spec (sublist 0 (i + 1) l) =
array_sum_even_indices_spec (sublist 0 i l) + Znth i l 0
```

when `i mod 2 = 0`. The odd branch preservation similarly needed:

```coq
array_sum_even_indices_spec (sublist 0 (i + 1) l) =
array_sum_even_indices_spec (sublist 0 i l)
```

when `i mod 2 <> 0`.

Fix: before editing the manual proof, I wrote `logs/proof_reasoning.md`. I then added reusable local helper lemmas:

```coq
array_sum_even_indices_spec_app_single_even
array_sum_even_indices_spec_app_single_odd
array_sum_even_indices_spec_sublist_snoc_even
array_sum_even_indices_spec_sublist_snoc_odd
```

The proof for `safety_wit_6` instantiates the prefix-bound hypothesis at `i + 1`, rewrites with `array_sum_even_indices_spec_sublist_snoc_even`, and closes the two integer range subgoals. The two loop-preservation obligations use the even and odd snoc lemmas. The initialization witness closes with `entailer!`, and the exit witness proves `i = n_pre`, rewrites `Zlength l = n_pre`, and uses `sublist_self`.

Result: `array_sum_even_indices_proof_manual.v` compiles, contains no `Admitted.`, and adds no `Axiom`.

## Issue 4: Coq intermediate files had to be cleaned after successful compile

Symptom: compiling generated Coq files produced non-`.v` artifacts under:

```text
output/verify_20260422_085356_array_sum_even_indices/coq/generated/
```

including `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files.

Fix: after `goal_check.v` compiled successfully, I removed all non-`.v` files under the current workspace's `coq/` directory:

```bash
find output/verify_20260422_085356_array_sum_even_indices/coq -type f ! -name '*.v' -delete
```

Result: `find output/verify_20260422_085356_array_sum_even_indices/coq -type f ! -name '*.v'` now returns no files.
