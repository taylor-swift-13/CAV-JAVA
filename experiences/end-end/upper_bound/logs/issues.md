## 2026-04-23 05:42 +0800 - Front-end `>` postcondition shape produced empty goal_check

- Phenomenon: after adding the upper-bound loop invariant and midpoint bridge, `symexec` reached the end of the target function but exited with status 1. `coq/generated/upper_bound_goal.v`, `upper_bound_proof_auto.v`, and `upper_bound_proof_manual.v` were generated, but `upper_bound_goal_check.v` was empty.
- Trigger command:

```text
QualifiedCProgramming/linux-binary/symexec \
  --input-file=annotated/verify_20260423_053250_upper_bound.c \
  --goal-file=output/verify_20260423_053250_upper_bound/coq/generated/upper_bound_goal.v \
  --proof-auto-file=output/verify_20260423_053250_upper_bound/coq/generated/upper_bound_proof_auto.v \
  --proof-manual-file=output/verify_20260423_053250_upper_bound/coq/generated/upper_bound_proof_manual.v \
  --goal-check-file=output/verify_20260423_053250_upper_bound/coq/generated/upper_bound_goal_check.v \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260423_053250_upper_bound \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE --no-exec-info
```

- Diagnostic from `logs/qcp_run.log`:

```text
The array i_94 of Znth is not a list type.
The type is Z
Start to symbolic execution on program : annotated/verify_20260423_053250_upper_bound.c
...
Symbolic Execution into function upper_bound
End of symbolic execution of function upper_bound
```

- Localization: the active annotated postcondition still used the comparison orientation `l[__return] > target`, while all invariant and assertion facts used the front-end-stable orientation `target < l[i]`.

```c
((__return == n) ||
 (__return < n && l[__return] > target)) &&
```

- Fix action: normalized only the active annotated copy, not `input/upper_bound.c`, to the equivalent comparison:

```c
((__return == n) ||
 (__return < n && target < l[__return])) &&
```

- Expected result: rerunning `symexec` from a clean `coq/generated/` set should generate a nonempty `upper_bound_goal_check.v` and allow the task to proceed to proof/compile.

Follow-up: the first normalization did not fix the failure. `upper_bound_goal.v` ended at an unfinished return witness:

```coq
Definition upper_bound_return_wit_1 :=
```

This showed the failure was specifically in return VC construction. The active annotated postcondition was therefore normalized from the scalar disjunction:

```c
((__return == n) ||
 (__return < n && target < l[__return]))
```

to the sorted-array-equivalent suffix quantifier already carried by the loop invariant:

```c
(forall (i: Z), (__return <= i && i < n) => target < l[i])
```

This keeps the intended upper-bound semantics under the contract's sortedness assumption and avoids scalar `l[__return]` in return VC generation.

Result after fix: rerunning `symexec` from a clean generated directory succeeded:

```text
Symbolic Execution into function upper_bound
End of symbolic execution of function upper_bound
Successfully finished symbolic execution
```

The generated files were complete:

```text
coq/generated/upper_bound_goal.v
coq/generated/upper_bound_proof_auto.v
coq/generated/upper_bound_proof_manual.v
coq/generated/upper_bound_goal_check.v
```

## 2026-04-23 05:52 +0800 - Manual midpoint and branch witnesses

- Phenomenon: `coq/generated/upper_bound_proof_manual.v` initially contained five admitted manual witnesses:

```coq
Lemma proof_of_upper_bound_safety_wit_2 : upper_bound_safety_wit_2.
Lemma proof_of_upper_bound_entail_wit_1 : upper_bound_entail_wit_1.
Lemma proof_of_upper_bound_entail_wit_2 : upper_bound_entail_wit_2.
Lemma proof_of_upper_bound_entail_wit_3_1 : upper_bound_entail_wit_3_1.
Lemma proof_of_upper_bound_entail_wit_3_2 : upper_bound_entail_wit_3_2.
```

- Localization: `upper_bound_safety_wit_2` was the midpoint signed-int range proof; `entail_wit_1` initialized the invariant; `entail_wit_2` established midpoint bounds; `entail_wit_3_1` preserved the suffix fact in the `a[mid] > target` branch; `entail_wit_3_2` preserved the prefix fact in the `a[mid] <= target` branch.
- Fix action: added a local quotient helper and proved the witnesses in `coq/generated/upper_bound_proof_manual.v`:

```coq
Lemma upper_bound_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.

Lemma proof_of_upper_bound_entail_wit_3_1 : upper_bound_entail_wit_3_1.
Proof.
  pre_process.
  assert (Hupper_new:
    forall j, mid <= j < n_pre -> target_pre < Znth j l 0).
  ...
Qed.

Lemma proof_of_upper_bound_entail_wit_3_2 : upper_bound_entail_wit_3_2.
Proof.
  pre_process.
  assert (Hlower_new:
    forall j, 0 <= j < mid + 1 -> Znth j l 0 <= target_pre).
  ...
Qed.
```

- Result: `coqc` compiled `upper_bound_goal.v`, `upper_bound_proof_auto.v`, `upper_bound_proof_manual.v`, and `upper_bound_goal_check.v` with no errors. `rg -n "Admitted\.|^\s*Axiom\b" coq/generated/upper_bound_proof_manual.v` returned no matches.

## 2026-04-23 05:53 +0800 - Cleanup completed

- Phenomenon: Coq compilation produced `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` intermediates under `coq/generated/`.
- Fix action: ran `find coq -type f ! -name '*.v' -delete` inside the workspace.
- Result: `find coq -type f ! -name '*.v' -print` returned no files. There was no workspace `input/` directory with non-`.c`/non-`.v` intermediates to clean.
