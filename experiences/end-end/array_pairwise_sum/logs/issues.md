# Verification Issues

## 2026-04-22 06:33 CST - Active annotated include paths were invalid for `symexec`

- Phenomenon: the first `symexec` run failed before VC generation. `logs/qcp_run.log` reported:

```text
fatal error: No such file ../verification_stdlib.h in search path in annotated/verify_20260422_063057_array_pairwise_sum.c:1:35
Start to symbolic execution on program : annotated/verify_20260422_063057_array_pairwise_sum.c
symexec_status=1
```

- Trigger: the input file uses `#include "../verification_stdlib.h"` because it lives under `input/`. The active verify copy lives under top-level `annotated/`, so `../verification_stdlib.h` resolves to `QualifiedCProgramming/QCP_examples/verification_stdlib.h`, which does not exist. Existing verified top-level annotated files use `../../verification_stdlib.h`, `../../verification_list.h`, and `../../int_array_def.h`.
- Localization: `annotated/verify_20260422_063057_array_pairwise_sum.c:1`.
- Fix action: updated only the active annotated C copy's includes:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```

- Result: after clearing stale generated files and rerunning `symexec` with `--flag=value` paths, symbolic execution succeeded and generated fresh Coq files.

## 2026-04-22 06:34 CST - Loop needed prefix/suffix annotation for output array update

- Phenomenon: the initial active annotated C had the raw loop only:

```c
for (i = 0; i < n; ++i) {
    out[i] = a[i] + b[i];
}
```

This gives the verifier no loop-head state describing how the partially written `out` relates to the postcondition witness `lr`.

- Trigger: `array_pairwise_sum` writes `out` one cell at a time while preserving `a` and `b`. The postcondition requires every final index to satisfy `lr[i] == la[i] + lb[i]`, so the loop invariant must preserve a computed prefix and untouched suffix.
- Localization: `annotated/verify_20260422_063057_array_pairwise_sum.c:29`.
- Fix action: added a loop invariant and two bridge assertions. The invariant tracks:

```c
exists l1 l2,
  0 <= i && i <= n@pre &&
  Zlength(l1) == i &&
  Zlength(l2) == n@pre - i &&
  (forall (k: Z), (0 <= k && k < i) => l1[k] == la[k] + lb[k]) &&
  (forall (k: Z), (0 <= k && k < n@pre - i) => l2[k] == lo[i + k]) &&
  IntArray::full(a, n@pre, la) *
  IntArray::full(b, n@pre, lb) *
  IntArray::full(out, n@pre, app(l1, l2))
```

The first `which implies` splits `a[i]`, `b[i]`, and `out[i]` into focused `data_at` cells. The second rebuilds `out` with an extended prefix `l1'` and suffix `sublist(i + 1, n@pre, lo)`.

- Result: `logs/qcp_run.log` ended with:

```text
End of symbolic execution of function array_pairwise_sum
Successfully finished symbolic execution
symexec_status=0
```

Generated files:

```text
coq/generated/array_pairwise_sum_goal.v
coq/generated/array_pairwise_sum_proof_auto.v
coq/generated/array_pairwise_sum_proof_manual.v
coq/generated/array_pairwise_sum_goal_check.v
```

## 2026-04-22 06:35 CST - Manual proof obligations remained after successful `symexec`

- Phenomenon: generated `coq/generated/array_pairwise_sum_proof_manual.v` contained six `Admitted.` placeholders:

```coq
proof_of_array_pairwise_sum_safety_wit_2
proof_of_array_pairwise_sum_entail_wit_1
proof_of_array_pairwise_sum_entail_wit_2
proof_of_array_pairwise_sum_return_wit_1
proof_of_array_pairwise_sum_which_implies_wit_1
proof_of_array_pairwise_sum_which_implies_wit_2
```

- Trigger: the generated VCs included signed-int range, invariant initialization/preservation, loop-exit postcondition, and array split/merge obligations that require manual list and separation-logic proof steps.
- Localization: `coq/generated/array_pairwise_sum_proof_manual.v:21`.
- Fix action: filled the six proofs using the existing prefix/suffix proof pattern for this function. Representative key proof fragments:

```coq
sep_apply (IntArray.full_split_to_missing_i a_pre i n_pre la 0).
sep_apply (IntArray.full_split_to_missing_i b_pre i n_pre lb 0).
sep_apply (IntArray.full_split_to_missing_i out_pre i n_pre (l1 ++ l2) 0).
```

and for the updated output list:

```coq
assert (l2 = sublist i n_pre lo) as Hl2.
Exists (l1 ++ cons (Znth i la 0 + Znth i lb 0) nil).
sep_apply (IntArray.missing_i_merge_to_full); [ | tauto].
rewrite replace_Znth_app_r by lia.
rewrite (sublist_split i n_pre (i + 1) lo) by (pose proof (Zlength_correct lo); lia).
```

- Result: `coq/generated/array_pairwise_sum_proof_manual.v` now has no `Admitted.`, no `admit`, no `Abort`, and no added `Axiom`.

## 2026-04-22 06:36 CST - Full Coq compile passed and intermediate artifacts were cleaned

- Command shape: full compile was run from `QualifiedCProgramming/SeparationLogic` with `_CoqProject`-style base `-R` paths plus:

```bash
-Q output/verify_20260422_063057_array_pairwise_sum/original ""
-R output/verify_20260422_063057_array_pairwise_sum/coq/generated SimpleC.EE.CAV.verify_20260422_063057_array_pairwise_sum
```

- Result: `logs/compile_full.log` recorded:

```text
compiled array_pairwise_sum_goal.v
compiled array_pairwise_sum_proof_auto.v
compiled array_pairwise_sum_proof_manual.v
compiled array_pairwise_sum_goal_check.v
compile_status=0
```

- Cleanup: after compilation, all non-`.v` artifacts under `coq/` were removed. A final `find coq -type f ! -name '*.v'` produced no output.
