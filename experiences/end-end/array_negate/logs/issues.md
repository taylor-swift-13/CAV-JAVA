# Verification Issues

## 2026-04-22 06:23:41 +0800 - Annotated include paths initially resolved outside `QCP_examples`

- Phenomenon: the first `symexec` run failed before VC generation and produced zero-byte generated Coq files.
- Trigger: the active annotated file was created by copying the input file's include paths:

```c
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"
```

From `annotated/verify_20260422_062136_array_negate.c`, `../verification_stdlib.h` resolves to `./../verification_stdlib.h` only if the file is one directory deeper than `annotated`; the actual verified examples in this repository use `../../verification_stdlib.h` from active annotated files.

- Localization:
  - annotated C: `annotated/verify_20260422_062136_array_negate.c`
  - symexec log: `output/verify_20260422_062136_array_negate/logs/qcp_run.log`

The concrete log excerpt was:

```text
fatal error: No such file ../verification_stdlib.h in search path in annotated/verify_20260422_062136_array_negate.c:1:35
symexec_status=1
```

- Fix action: updated only the active annotated working copy to use the repository's established annotated include layout:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```

- Result: this was a front-end include-path problem, not a contract or proof failure. After the include-path correction, the next action is to clear the zero-byte generated files and rerun `symexec` against the same annotated workspace file.

## 2026-04-22 06:24:25 +0800 - Loop invariant generated fresh Coq files

- Phenomenon: after adding the prefix/suffix loop invariant and fixing the annotated include paths, `symexec` completed successfully and generated non-empty Coq files.
- Trigger: `array_negate` writes `out` element by element, so the loop head needs to preserve the input array and summarize the output as a transformed prefix plus original suffix:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      out == out@pre &&
      n == n@pre &&
      n@pre == Zlength(la) &&
      n@pre == Zlength(lo) &&
      Zlength(l1) == i &&
      Zlength(l2) == n@pre - i &&
      (forall (t: Z), (0 <= t && t < i) => l1[t] == -la[t]) &&
      (forall (t: Z), (0 <= t && t < n@pre - i) => l2[t] == lo[i + t]) &&
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, app(l1, l2))
*/
```

- Localization:
  - annotated C: `annotated/verify_20260422_062136_array_negate.c`
  - symexec log: `output/verify_20260422_062136_array_negate/logs/qcp_run.log`

- Fix action: cleared stale generated targets and ran `symexec` with:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260422_062136_array_negate.c \
  --goal-file=output/verify_20260422_062136_array_negate/coq/generated/array_negate_goal.v \
  --proof-auto-file=output/verify_20260422_062136_array_negate/coq/generated/array_negate_proof_auto.v \
  --proof-manual-file=output/verify_20260422_062136_array_negate/coq/generated/array_negate_proof_manual.v \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_062136_array_negate \
  --no-exec-info
```

- Result: `logs/qcp_run.log` ended with:

```text
End of symbolic execution of function array_negate
Successfully finished symbolic execution
symexec_status=0
```

The generated files were `array_negate_goal.v`, `array_negate_proof_auto.v`, `array_negate_proof_manual.v`, and `array_negate_goal_check.v`.

## 2026-04-22 06:27:48 +0800 - Manual proof obligations were discharged

- Phenomenon: `array_negate_proof_manual.v` initially contained four `Admitted.` placeholders:

```coq
proof_of_array_negate_safety_wit_2
proof_of_array_negate_entail_wit_1
proof_of_array_negate_entail_wit_2
proof_of_array_negate_return_wit_1
```

- Trigger: the generated witnesses needed manual pure arithmetic and list normalization:
  - safety: prove `Znth i la 0 <> INT_MIN` from the negation overflow guard.
  - initial invariant: instantiate the prefix as `nil` and suffix as `lo`.
  - loop preservation: normalize `replace_Znth i (-(Znth i la 0)) (l1 ++ l2)` into `(l1 ++ [-(Znth i la 0)]) ++ sublist (i + 1) n lo`.
  - return: prove `i = n`, `l2 = nil`, and use `lr = l1`.

- Localization:
  - proof file: `output/verify_20260422_062136_array_negate/coq/generated/array_negate_proof_manual.v`
  - proof reasoning: `output/verify_20260422_062136_array_negate/logs/proof_reasoning.md`
  - compile log: `output/verify_20260422_062136_array_negate/logs/compile.log`

- Fix action: replaced all four placeholders with explicit scripts adapted from the existing prefix/suffix `array_scale` proof pattern. Two proof issues appeared and were fixed:
  - The first safety proof tried to match on `INT_MIN`/`INT_MAX`, but `pre_process` had simplified them to numerals; the fix was to use the generated overflow hypothesis directly:

```coq
pose proof (H11 i ltac:(lia)) as Hrange.
lia.
```

  - The return proof had a range `0 <= i < n_pre` but the prefix hypothesis expected `0 <= i < Zlength l1`; the fix was to rewrite with the known exit length:

```coq
apply H6.
rewrite H12.
exact Hi.
```

- Result: `proof_manual.v` contains no `Admitted.` and no new `Axiom`, and the final compile log records:

```text
compiled array_negate_goal.v
compiled array_negate_proof_auto.v
compiled array_negate_proof_manual.v
compiled array_negate_goal_check.v
compile_status=0
```

## 2026-04-22 06:27:48 +0800 - Coq compile cleanup completed

- Phenomenon: successful Coq compilation left `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` intermediates under `coq/generated/`.
- Trigger: Verify completion requires the current workspace's `coq/` tree to contain only source `.v` files after compilation has succeeded.
- Localization: `output/verify_20260422_062136_array_negate/coq/generated/`.
- Fix action: after `goal_check.v` compiled successfully, removed all non-`.v` files under the workspace `coq/` tree.
- Result: the remaining Coq files are exactly:

```text
coq/generated/array_negate_goal.v
coq/generated/array_negate_goal_check.v
coq/generated/array_negate_proof_auto.v
coq/generated/array_negate_proof_manual.v
```
