## 2026-04-22 08:08 CST - Workspace fingerprint initially had empty semantic metadata

- Phenomenon: `logs/workspace_fingerprint.json` was initialized with an empty `semantic_description` and `{}` keywords.
- Trigger: early verify workflow setup before running annotation or proof work.
- Location: `logs/workspace_fingerprint.json`.
- Fix action: read the controlled vocabulary in `doc/retrieval/INDEX.md`, then updated the fingerprint with a non-empty description of the elementwise array scaling loop and controlled keywords only:

```json
"semantic_description": "array_scale verifies a single for-loop that preserves the input integer array a and writes every output element out[i] to la[i] * k. ...",
"keywords": {
  "control_flow": "for_loop",
  "data_shape": ["array", "pointer"],
  "semantic_intent": "preserve_input",
  "proof_pattern": ["loop_invariant", "range_bound", "heap_reasoning"],
  "numeric_properties": ["overflow_guard", "int_range", "nonnegative_input"],
  "edge_case_behavior": "empty_loop_possible"
}
```

- Result: the fingerprint is now non-empty and, after final verification, also records `verification_status` with `goal_check_passed` and `proof_check_passed`.

## 2026-04-22 08:09 CST - The unannotated loop needed a prefix/suffix output invariant

- Phenomenon: the active annotated file initially matched the input loop and had no `Inv`:

```c
for (i = 0; i < n; ++i) {
    out[i] = a[i] * k;
}
```

- Trigger: `array_scale` writes the output array progressively, so symbolic execution needs a loop-head summary that preserves the input heap and records which output prefix has already been written.
- Location: `annotated/verify_20260422_080741_array_scale.c`, before the `for` loop.
- Fix action: added an invariant with ghost lists `l1` and `l2`, where `l1` is the completed prefix satisfying `l1[t] == la[t] * k@pre`, `l2` is the untouched suffix satisfying `l2[t] == lo[i + t]`, and the output heap is `IntArray::full(out, n@pre, app(l1, l2))`.
- Result: the invariant was strong enough for final `symexec`; no loop-exit assertion was needed because `i >= n@pre` plus `i <= n@pre` yields the completed-prefix case at return.

## 2026-04-22 08:10 CST - First `symexec` failed on active annotated include paths

- Phenomenon: the first symbolic execution attempt did not reach VC generation.
- Trigger: the active annotated copy used input-style includes:

```c
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"
```

- Location: `logs/qcp_run.log` from the first run and line 1 of the active annotated file.
- Error text:

```text
fatal error: No such file ../verification_stdlib.h in search path in annotated/verify_20260422_080741_array_scale.c:1:35
symexec_status=1
```

- Fix action: changed only the active annotated working copy to the include layout used by verified examples:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```

- Result: the next `symexec` reached the loop body and exposed the next annotation issue, confirming the include failure was a front-end path issue rather than a contract or proof failure.

## 2026-04-22 08:10 CST - In-body `which implies` bridge dropped scalar `k`

- Phenomenon: after fixing include paths, `symexec` failed at the post-assignment bridge around the statement `out[i] = a[i] * k;`.
- Trigger: the bridge assertion exposed the `a[i]` and `out[i]` array cells but did not preserve the local scalar storage for `k`. The verifier evaluated the assignment result as a product with `NULL` instead of `k_pre`.
- Location: active annotated file line 63 at the time of failure; `logs/qcp_run.log`.
- Key diagnostic:

```text
store ( (out_83_pre + (i_128_value * (Size_of signed int))) , ((la_95_free[i_128_value]) * NULL) , signed int )
...
Partial Solve Failed for Partial Implies
The Sep is:
SEP[store(n_93_addr , Zlength(Z, la_95_free) , signed int); store(k_87_addr , k_86_pre , signed int)]
```

- Fix action: removed the two in-body `which implies` bridge assertions and kept the scalar-stability fact `k == k@pre` in the loop invariant. This matches the stable pattern from scalar examples that let normal symbolic execution handle scalar reads instead of narrowing the heap state around the statement.
- Result: rerunning `symexec` from a clean generated directory succeeded:

```text
End of symbolic execution of function array_scale
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-22 08:12 CST - Manual proof obligations remained after successful `symexec`

- Phenomenon: generated `coq/generated/array_scale_proof_manual.v` contained four admitted manual lemmas:

```coq
proof_of_array_scale_safety_wit_2
proof_of_array_scale_entail_wit_1
proof_of_array_scale_entail_wit_2
proof_of_array_scale_return_wit_1
```

- Trigger: successful symbolic execution generated list and arithmetic obligations for the prefix/suffix invariant.
- Location: `coq/generated/array_scale_proof_manual.v`.
- Fix action: replaced the four `Admitted.` bodies with concrete proofs. The loop-preservation proof normalizes the output list by proving the old suffix equals `sublist i_2 n_pre lo`, choosing `l1_2 ++ [Znth i_2 la 0 * k_pre]` as the new prefix, rewriting `replace_Znth_app_r`, and splitting the new prefix relation into `t < i_2` and `t = i_2`.
- Result: `array_scale_proof_manual.v` compiled and contains no remaining `Admitted.` or top-level `Axiom` declarations.

## 2026-04-22 08:13 CST - Full compile replay and cleanup completed

- Phenomenon: final verification requires more than successful manual proof compilation; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all must compile under the workspace load path, then non-`.v` Coq artifacts must be removed.
- Trigger: final completion check.
- Location: `logs/compile.log` and `coq/generated/`.
- Fix action: ran the fail-fast compile template from `QualifiedCProgramming/SeparationLogic`.
- Compile result:

```text
compiled array_scale_goal.v
compiled array_scale_proof_auto.v
compiled array_scale_proof_manual.v
compiled array_scale_goal_check.v
```

- Cleanup result: after deleting non-`.v` files under `coq/`, the remaining files are:

```text
coq/generated/array_scale_goal.v
coq/generated/array_scale_goal_check.v
coq/generated/array_scale_proof_auto.v
coq/generated/array_scale_proof_manual.v
```

- Result: final verification succeeded for the latest annotated file and current generated Coq files.
