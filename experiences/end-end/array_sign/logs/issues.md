# Verify Issues

## Fingerprint initially had empty semantic metadata

- Phenomenon: `logs/workspace_fingerprint.json` was still in its initialized state with `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the workspace was created before the verify run but had not yet been classified for retrieval.
- Location: `output/verify_20260422_083344_array_sign/logs/workspace_fingerprint.json`.
- Fix action: read `doc/retrieval/INDEX.md`, then filled a non-empty description of the array sign scan and used only controlled vocabulary keys and values:

```json
"algorithm_family": "selection",
"control_flow": ["for_loop", "if"],
"data_shape": ["array", "pointer"],
"semantic_intent": ["preserve_input", "in_place_update"],
"proof_pattern": ["loop_invariant", "case_split", "heap_reasoning"],
"numeric_properties": "int_range",
"edge_case_behavior": "empty_loop_possible"
```

- Result: the fingerprint became usable for retrieval. After final verification it was extended with controlled `verification_status` values `goal_check_passed`, `proof_check_passed`, and `auto_proof_contains_admitted`.

## Loop needed a prefix/suffix invariant and frontend-friendly single-write shape

- Phenomenon: the active annotated file initially had no loop invariant around `for (i = 0; i < n; ++i)`, so `symexec` would not have a stable assertion describing the already-written output prefix or the still-original suffix.
- Trigger: the postcondition is a full-array relation over all indices, while the loop updates one output cell per iteration according to a three-way sign case.
- Location: `annotated/verify_20260422_083344_array_sign.c`, the single loop in `array_sign`.
- Fix action: added a loop invariant with existential lists `l1` and `l2`. `l1` is the processed prefix of length `i`; `l2` is the original suffix of length `n@pre - i`; the output heap is `IntArray::full(out, n@pre, app(l1, l2))`; and the sign relation is represented by three separate quantified implications:

```c
(forall (t: Z), (0 <= t && t < i && la[t] > 0) => l1[t] == 1) &&
(forall (t: Z), (0 <= t && t < i && la[t] < 0) => l1[t] == -1) &&
(forall (t: Z), (0 <= t && t < i && la[t] == 0) => l1[t] == 0)
```

The active annotated working copy was also normalized to compute `v = a[i]`, compute scalar `s` in the branch, and perform one `out[i] = s` after the branch. The bridge before the write exposes `IntArray::missing_i` plus `data_at`; the bridge after the write rebuilds the next `IntArray::full` with an existential `l1'`.

- Result: after these annotations and the include-path fix below, `QualifiedCProgramming/linux-binary/symexec` completed successfully and generated `array_sign_goal.v`, `array_sign_proof_auto.v`, `array_sign_proof_manual.v`, and `array_sign_goal_check.v`.

## Annotated include paths inherited input-relative paths

- Phenomenon: the first `symexec` run exited with status 1 and `logs/qcp_run.log` reported:

```text
fatal error: No such file ../verification_stdlib.h in search path in annotated/verify_20260422_083344_array_sign.c:1:35
```

- Trigger: `input/array_sign.c` uses `#include "../verification_stdlib.h"` because it is under `CAV/input`. The active annotated file is under `CAV/annotated`, so the same relative include incorrectly points to `CAV/verification_stdlib.h`. The headers actually live under `QualifiedCProgramming/QCP_examples/`.
- Location: the first three include lines of `annotated/verify_20260422_083344_array_sign.c`.
- Fix action: changed only the active annotated working copy to:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```

- Result: the next clean `symexec` run succeeded with `symexec_status=0`.

## Manual proof obligation for invariant initialization

- Phenomenon: after successful `symexec`, `coq/generated/array_sign_proof_manual.v` contained one admitted manual obligation:

```coq
Lemma proof_of_array_sign_entail_wit_1 : array_sign_entail_wit_1.
Proof. Admitted.
```

- Trigger: this witness initializes the loop invariant from the function precondition. It needs concrete witnesses for the invariant's `EX l2 l1`.
- Location: `output/verify_20260422_083344_array_sign/coq/generated/array_sign_proof_manual.v`.
- Fix action: instantiated `l2 = lo` and `l1 = nil`, then used simplification and `entailer!`:

```coq
Lemma proof_of_array_sign_entail_wit_1 : array_sign_entail_wit_1.
Proof.
  unfold array_sign_entail_wit_1.
  intros.
  Exists lo nil.
  simpl.
  entailer!.
Qed.
```

- Result: `array_sign_proof_manual.v` compiled successfully, `array_sign_goal_check.v` compiled successfully, and `proof_manual.v` contains no `Admitted.` and no added top-level `Axiom`.

## Full compile replay and cleanup were required before success

- Phenomenon: successful symbolic execution alone is not enough for the verify workflow; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must all compile under the workspace logical path, and non-`.v` Coq intermediates must be removed afterward.
- Trigger: `goal_check.v` imports `array_sign_goal`, `array_sign_proof_auto`, and `array_sign_proof_manual` under `SimpleC.EE.CAV.verify_20260422_083344_array_sign`.
- Location: compile log `output/verify_20260422_083344_array_sign/logs/compile_full.log` and generated directory `output/verify_20260422_083344_array_sign/coq/generated/`.
- Fix action: ran the documented `coqc` sequence from `QualifiedCProgramming/SeparationLogic` with `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_083344_array_sign`, then deleted all non-`.v` files under `coq/`.
- Result: the compile log contains:

```text
compiled array_sign_goal.v
compiled array_sign_proof_auto.v
compiled array_sign_proof_manual.v
compiled array_sign_goal_check.v
```

After cleanup, `find coq -type f ! -name '*.v'` returned no files.
