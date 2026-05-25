# Verify Issues

## 2026-04-22 symexec search path run from wrong directory

Phenomenon: the first `symexec` invocation failed before parsing the annotated program:

```text
symexec_start=2026-04-22 18:29:36 +0800
folder path QCP_examples/ does not exist
symexec_status=1
```

Trigger: I ran `linux-binary/symexec ... -slp QCP_examples/ SimpleC.EE ...` from `QualifiedCProgramming/QCP_examples/CAV`. The `-slp QCP_examples/` path is relative to `QualifiedCProgramming`, not to `CAV/`.

Fix: reran the same command from `QualifiedCProgramming`, still writing generated files only under `output/verify_20260422_182720_lcm_simple/coq/generated/` and using the active annotated file `QCP_examples/CAV/annotated/verify_20260422_182720_lcm_simple.c`.

Result:

```text
Symbolic Execution into function lcm_simple
End of symbolic execution of function lcm_simple
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-22 compile template run from wrong directory

Phenomenon: the first Coq replay used the correct `-R` arguments but ran from `QualifiedCProgramming`, so paths from `_CoqProject` such as `auxlibs` and `examples` did not resolve:

```text
Warning: Cannot open auxlibs [cannot-open-path,filesystem,default]
Error: Cannot find a physical path bound to logical path
int_auto with prefix AUXLib.
```

Trigger: compile commands like `coqc -R auxlibs AUXLib ...` must be executed from `QualifiedCProgramming/SeparationLogic`, where those relative directories exist.

Fix: reran the full compile sequence from `QualifiedCProgramming/SeparationLogic` with the same workspace-specific load paths:

```bash
-Q "$ORIG" ""
-R "$GEN" "SimpleC.EE.CAV.verify_20260422_182720_lcm_simple"
```

Result: load-path errors disappeared; later failures were genuine manual proof issues in `lcm_simple_proof_manual.v`.

## 2026-04-22 LCM positivity helper was circular

Phenomenon: compiling `lcm_simple_proof_manual.v` failed at the first version of `lcm_simple_value_pos`:

```text
File ".../lcm_simple_proof_manual.v", line 34, characters 15-18:
Error: Tactic failure: Cannot find witness.
```

Failing fragment:

```coq
pose proof (Z.divide_pos_le a (Z.lcm a b)) as Hle.
assert (a <= Z.lcm a b).
{ apply Hle; lia. }
```

Cause: `Z.divide_pos_le a (Z.lcm a b)` requires `0 < Z.lcm a b`, which was exactly the lemma being proved.

Fix: changed the positivity proof to use `Z.lcm_nonneg` and contradiction through `Z.lcm_eq_0`. For positive `a` and `b`, `Z.lcm a b = 0` would imply `a = 0 \/ b = 0`, impossible by the preconditions.

Result: `lcm_simple_value_pos` compiled, and `lcm_simple_value_ge_left` could then safely use `Z.divide_pos_le`.

## 2026-04-22 generated modulo notation is `Z.rem`, not `Z.mod`

Phenomenon: after adding helper lemmas, `proof_of_lcm_simple_safety_wit_3` failed with:

```text
The term "H" has type "x % b_pre <> 0" while it is expected to have type
"x mod b_pre <> 0"
```

Trigger: the generated VC for C `%` uses Coq `Z.rem` notation, printed as `x % b_pre`, while my helper lemma premises initially used `x mod b`.

Fix: changed helper statements from `x mod b` to `Z.rem x b`, and changed divisibility conversions from `Z.mod_divide` to `Z.rem_divide`:

```coq
Z.rem x b <> 0
Z.rem x b = 0
apply Z.rem_divide; try lia.
```

Result: the generated branch fact `H : x % b_pre <> 0` and exit fact `H : x % b_pre = 0` matched the helper lemmas.

## 2026-04-22 `entailer!` left fewer pure subgoals than expected

Phenomenon: I initially wrote bullet scripts for every pure conjunct in `lcm_simple_entail_wit_1` and `lcm_simple_entail_wit_2`. Coq reported focus errors and failed arithmetic bullets, including:

```text
Error: [Focus] Wrong bullet -: No more goals.
Error: Tactic failure: Goal is not an equation (of expected equality) eq.
```

Cause: after `pre_process`, `Exists`, and `entailer!`, most pure conjuncts were already solved. For `entail_wit_1`, the only remaining goal was:

```coq
a_pre <= lcm_simple_value a_pre b_pre
```

For `entail_wit_2`, the only remaining goal was:

```coq
x + a_pre <= lcm_simple_value a_pre b_pre
```

Fix: simplified the proofs to match the actual remaining goals:

```coq
apply lcm_simple_value_ge_left; lia.
apply (lcm_simple_next_le_lcm a_pre b_pre x k_2); try lia; auto.
```

Result: both entailment witnesses compile.

## 2026-04-22 return witness needed separation-logic cleanup before pure helper

Phenomenon: applying `lcm_simple_exit_eq` directly after unfolding `lcm_simple_spec` failed:

```text
Unable to unify "? = lcm_simple_value ? ?" with
"forall m : model, emp m -> ([|x = lcm_simple_value a_pre b_pre|] && emp) m".
```

Cause: the goal was still a separation-logic entailment containing `[| ... |] && emp`, not the pure equality itself.

Fix: inserted `entailer!` after unfolding the spec:

```coq
pre_process.
unfold lcm_simple_spec.
entailer!.
apply lcm_simple_exit_eq with (k := k); auto.
```

Result: `proof_of_lcm_simple_return_wit_1` compiled, and the final `lcm_simple_goal_check.v` compiled successfully.
