# Verify issues: merge_sorted_arrays

## Include path failure before symbolic execution

- Symptom: the first local `symexec` run failed before VC generation with:

```text
fatal error: No such file ../verification_stdlib.h in search path in QCP_examples/CAV/annotated/verify_20260422_194235_merge_sorted_arrays.c:1:35
```

- Trigger: the active annotated file is stored at `QCP_examples/CAV/annotated/verify_20260422_194235_merge_sorted_arrays.c`, while the copied input kept includes such as `#include "../verification_stdlib.h"`. From `CAV/annotated`, that path resolves to `QCP_examples/CAV/verification_stdlib.h`, which does not exist; the shared headers live one level higher under `QCP_examples/`.
- Fix: changed only the active annotated C file, not `input/`, to match existing verified annotated examples:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```

- Result after fix: pending rerun of `symexec`; this issue is expected to be resolved because the same include depth is used by other active annotated files under `CAV/annotated/`.

## Disjunction in second-loop invariant made a valid phase impossible

- Symptom: after preprocessing was fixed, `symexec` failed at the invariant for `while (i < n)` with `Partial Solve Invariant Error` at line 108 of the active annotated file.
- Trigger: the main loop can exit with `j == m` and `i < n`; that is exactly the path where the second loop copies the rest of `a`. The left side in the failed entailment showed `j_149_value >= m_90_pre`, `j_149_value <= m_90_pre`, and `i_150_value < n_96_pre`.
- Bad annotation:

```c
(i == n || j == m) &&
((i < n) => j == m) &&
```

- Why it failed: the front end generated a target requiring `i_210_value == n_96_pre` for the second-loop invariant, which is false on the valid `j == m && i < n` branch.
- Fix: removed the disjunction and kept only the body-relevant implication:

```c
((i < n) => j == m) &&
```

- Result after fix: pending rerun of `symexec`.

## Strong quantified merge history made symexec CPU-bound

- Symptom: after removing the second-loop disjunction, `symexec` ran for several minutes with no log growth. The run had to be killed and `logs/qcp_run.log` was marked with `symexec_status=124`.
- Trigger: each loop invariant carried two nested quantified cross-boundary ordering implications over consumed and future portions of the input arrays.
- Problematic annotation shape:

```c
(forall (bi: Z) (ai: Z),
  (0 <= bi && bi < j && i <= ai && ai < n) =>
    Znth(bi, lb, 0) < Znth(ai, la, 0)) &&
(forall (ai: Z) (bi: Z),
  (0 <= ai && ai < i && j <= bi && bi < m) =>
    Znth(ai, la, 0) <= Znth(bi, lb, 0)) &&
```

- Fix: replaced those front-end-heavy history facts with a semantic decomposition equality plus prefix length:

```c
Zlength(merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb))) == k &&
merge_sorted_arrays_spec(la, lb) ==
  app(merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)),
      merge_sorted_arrays_spec(sublist(i, n, la), sublist(j, m, lb))) &&
```

- Expected result: `symexec` should generate VCs instead of trying to solve quantified merge history during symbolic execution. Remaining merge decomposition obligations should be handled as pure Coq list lemmas in manual proof.

## Recursive merge decomposition still timed out in symexec

- Symptom: the invariant using a single semantic decomposition equality still did not produce VC files within a 240-second `timeout`; `qcp_run.log` ended with `symexec_status=124`.
- Trigger: the invariant still contained recursive `merge_sorted_arrays_spec` calls inside a top-level equality over `app(...)`.
- Problematic annotation:

```c
merge_sorted_arrays_spec(la, lb) ==
  app(merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)),
      merge_sorted_arrays_spec(sublist(i, n, la), sublist(j, m, lb))) &&
```

- Fix: replaced the recursive output-prefix expression with an existential `ldone` list, its length, and an elementwise relation to the final specification:

```c
exists ldone,
Zlength(ldone) == k &&
(forall (p: Z),
  (0 <= p && p < k) =>
    Znth(p, ldone, 0) == Znth(p, merge_sorted_arrays_spec(la, lb), 0)) &&
IntArray::full(out, n + m, app(ldone, sublist(k, n + m, lo)))
```

- Expected result: heap updates should become structural enough for VC generation, with the remaining selected-element and final extensional-list facts deferred to manual Coq proof.

## Existential prefix with quantified final-spec relation still timed out

- Symptom: after switching to `exists ldone`, `symexec` still timed out under a 120-second bound and wrote `symexec_status=124`.
- Trigger: the invariant retained a quantified relation comparing every written prefix element to `merge_sorted_arrays_spec(la, lb)`.
- Problematic annotation:

```c
(forall (p: Z),
  (0 <= p && p < k) =>
    Znth(p, ldone, 0) == Znth(p, merge_sorted_arrays_spec(la, lb), 0)) &&
```

- Fix: removed the existential and quantified relation, and used the final-spec prefix directly in the output heap:

```c
IntArray::full(out, n + m,
  app(sublist(0, k, merge_sorted_arrays_spec(la, lb)),
      sublist(k, n + m, lo)))
```

- Expected result: the front end should track heap shape with `sublist`/`app` only; selected-element correctness should appear as manual pure/list VCs.

## Final blocker: recursive merge spec in loop-level output state prevents complete symexec

- Symptom: the final attempted invariant shape, with output heap written as `app(sublist(0, k, merge_sorted_arrays_spec(la, lb)), sublist(k, n + m, lo))`, also timed out under a 120-second `timeout`.
- Triggering command shape:

```text
timeout 120 QualifiedCProgramming/linux-binary/symexec \
  --goal-file=QCP_examples/CAV/output/verify_20260422_194235_merge_sorted_arrays/coq/generated/merge_sorted_arrays_goal.v \
  --proof-auto-file=QCP_examples/CAV/output/verify_20260422_194235_merge_sorted_arrays/coq/generated/merge_sorted_arrays_proof_auto.v \
  --proof-manual-file=QCP_examples/CAV/output/verify_20260422_194235_merge_sorted_arrays/coq/generated/merge_sorted_arrays_proof_manual.v \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_194235_merge_sorted_arrays \
  -slp QCP_examples/ SimpleC.EE \
  --input-file=QCP_examples/CAV/annotated/verify_20260422_194235_merge_sorted_arrays.c \
  --no-exec-info
```

- Final log result:

```text
symexec_start=2026-04-22 20:01:00 +0800
symexec_end=2026-04-22 20:03:00 +0800
symexec_status=124
```

- Generated files: the timeout left zero-byte files at `coq/generated/merge_sorted_arrays_goal.v`, `merge_sorted_arrays_proof_auto.v`, `merge_sorted_arrays_proof_manual.v`, and `merge_sorted_arrays_goal_check.v`. They are not complete VCs and must not be treated as a successful `symexec` result.
- Status: verification failed in the symbolic-execution stage. No manual Coq proof was attempted because there is no complete current witness list.

## 2026-04-22 retry: restored archived prefix invariant and symexec succeeded

- Symptom before fix: the current active annotation used the heap shape below in all three loop invariants, and `symexec` timed out with status 124 while leaving zero-byte generated files:

```c
IntArray::full(out, n + m,
  app(sublist(0, k, merge_sorted_arrays_spec(la, lb)),
      sublist(k, n + m, lo)))
```

Latest failing log before this retry:

```text
symexec_start=2026-04-22 20:01:00 +0800
symexec_end=2026-04-22 20:03:00 +0800
symexec_status=124
```

- Localization: `annotated/verify_20260422_194235_merge_sorted_arrays.c`, the three loop invariants before the main merge loop and two tail-copy loops.
- Evidence used for repair: the archived same-function workspace `./archieve/examples_backup_20260422_011624/merge_sorted_arrays/` has identical `merge_sorted_arrays.v`, identical generated `merge_sorted_arrays_goal.v`, and a completed manual proof. Its annotated C uses an existential written prefix and explicit cross-boundary `Znth` facts.
- Fix action: replaced the final-spec-sublist heap expression with:

```c
exists lout_done,
Zlength(lout_done) == k &&
lout_done == merge_sorted_arrays_spec(sublist(0, i, la), sublist(0, j, lb)) &&
IntArray::full(out, n + m, app(lout_done, sublist(k, n + m, lo)))
```

and restored the merge history facts:

```c
(forall (bp: Z) (ai: Z),
  (0 <= bp && bp < j && i <= ai && ai < n) =>
    Znth(bp, lb, 0) < Znth(ai, la, 0)) &&
(forall (ap: Z) (bi: Z),
  (0 <= ap && ap < i && j <= bi && bi < m) =>
    Znth(ap, la, 0) <= Znth(bi, lb, 0)) &&
```

- Result after fix: after clearing generated files and rerunning `QualifiedCProgramming/linux-binary/symexec` with `--flag=value` arguments, symbolic execution completed:

```text
Start to symbolic execution on program : QCP_examples/CAV/annotated/verify_20260422_194235_merge_sorted_arrays.c
Symbolic Execution into function merge_sorted_arrays
End of symbolic execution of function merge_sorted_arrays
Successfully finished symbolic execution
```

The fresh generated file sizes were:

```text
98698 merge_sorted_arrays_goal.v
 3219 merge_sorted_arrays_proof_auto.v
12918 merge_sorted_arrays_proof_manual.v after manual proof repair
  498 merge_sorted_arrays_goal_check.v
```

## 2026-04-22 retry: manual proof reused from byte-identical archived goal

- Symptom after successful `symexec`: fresh `coq/generated/merge_sorted_arrays_proof_manual.v` contained ten generated `Admitted.` placeholders for `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_3_1`, `entail_wit_3_2`, `entail_wit_4`, `entail_wit_5_1`, `entail_wit_5_2`, `entail_wit_6`, and `return_wit_1`.
- Localization: `output/verify_20260422_194235_merge_sorted_arrays/coq/generated/merge_sorted_arrays_proof_manual.v`.
- Evidence that reuse is valid: `diff -u` between the current `merge_sorted_arrays_goal.v` and the archived successful `merge_sorted_arrays_goal.v` produced no output, so the witness definitions are byte-identical. The only required proof-file change was the import path from `verify_20260421_144632_merge_sorted_arrays` to `verify_20260422_194235_merge_sorted_arrays`.
- Fix action: reused the archived helper lemmas and witness proofs, including `replace_Znth_app_suffix_head_Z`, `sublist_prefix_snoc_Z`, `merge_app_a_last`, `merge_app_b_last`, `Forall_sublist0_Znth_le_value`, `Forall_sublist0_Znth_lt_value`, and `Zlength_merge_sorted_arrays_spec`.
- Result after fix: `rg -n 'Admitted\.|^\s*Axiom\b' coq/generated/merge_sorted_arrays_proof_manual.v` found no forbidden lines, and full Coq replay succeeded:

```text
compiled original/merge_sorted_arrays.v
compiled merge_sorted_arrays_goal.v
compiled merge_sorted_arrays_proof_auto.v
compiled merge_sorted_arrays_proof_manual.v
compiled merge_sorted_arrays_goal_check.v
compile_status: 0
```

## 2026-04-22 retry: cleanup after successful compile

- Trigger: the successful Coq replay produced `.vo`, `.glob`, `.vos`, `.vok`, and `.aux` files under `output/verify_20260422_194235_merge_sorted_arrays/coq/generated/`.
- Fix action: deleted all non-`.v` files under the current workspace `coq/` directory, and checked `input/` for non-`.c`/non-`.v` files.
- Result: follow-up `find output/verify_20260422_194235_merge_sorted_arrays/coq -type f ! -name '*.v'` and `find input -maxdepth 1 -type f ! -name '*.c' ! -name '*.v'` produced no output.
