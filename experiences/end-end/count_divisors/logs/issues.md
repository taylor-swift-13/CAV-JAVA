# Verify Issues

## `Z.to_nat` cannot be used directly in C annotations

- Phenomenon: the first `symexec` run after adding the divisor-count invariant failed before generating nonempty Coq files. The generated files under `coq/generated/` were all zero bytes.
- Trigger command shape:

```bash
QualifiedCProgramming/linux-binary/symexec \
  --goal-file=.../count_divisors_goal.v \
  --proof-auto-file=.../count_divisors_proof_auto.v \
  --proof-manual-file=.../count_divisors_proof_manual.v \
  --coq-logic-path=SimpleC.EE.CAV.verify_20260422_145616_count_divisors \
  -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE \
  --input-file=annotated/verify_20260422_145616_count_divisors.c \
  --no-exec-info
```

- Relevant annotation fragment:

```c
cnt == count_divisors_upto(n, Z.to_nat(d - 1))
```

- Error from `logs/qcp_run.log`:

```text
fatal error: Use of undeclared identifier `Z' in annotated/verify_20260422_145616_count_divisors.c:24:4
```

- Cause: the C annotation parser does not accept the qualified Coq identifier `Z.to_nat` as a term-level function call; it parses `Z` as an undeclared C/annotation identifier before Coq typechecking is reached.
- Fix action: add a workspace-local Coq helper in `coq/deps/count_divisors_helper.v` defining `count_divisors_upto_z n fuel := count_divisors_upto n (Z.to_nat fuel)`, import it from the annotated C file, and rewrite the invariant to call `count_divisors_upto_z(n, d - 1)` instead of using `Z.to_nat` directly.
- Expected result after fix: `symexec` should get past annotation parsing and either generate VCs or expose the next invariant/proof issue.
- Result: after this change, `symexec` succeeded and generated nonempty `count_divisors_goal.v`, `count_divisors_proof_auto.v`, `count_divisors_proof_manual.v`, and `count_divisors_goal_check.v`.

## Initial invariant bound was too weak for the dividing branch

- Phenomenon: after the first successful `symexec`, manual proof replay of `count_divisors_entail_wit_2_1` left the pure goal `cnt + 1 <= n_pre`.
- Triggering generated goal fragment:

```coq
[| cnt <= n_pre |]
[| cnt = count_divisors_upto_z n_pre (d - 1) |]
|--
[| cnt + 1 <= n_pre |]
```

- Cause: `cnt <= n_pre` alone is too weak for the branch where `cnt++` executes. The loop semantics also require that before processing candidate `d`, at most `d - 1` candidates have been counted.
- Fix action: strengthened the loop invariant in `annotated/verify_20260422_145616_count_divisors.c` from:

```c
0 <= cnt && cnt <= n &&
cnt == count_divisors_upto_z(n, d - 1)
```

to:

```c
0 <= cnt && cnt <= d - 1 && cnt <= n &&
cnt == count_divisors_upto_z(n, d - 1)
```

- Result: rerunning `symexec` succeeded, and the regenerated preservation VC had enough pure facts to prove both `cnt + 1 <= (d + 1) - 1` and `cnt + 1 <= n_pre`.

## Manual proof normalization details

- Phenomenon: the generated helper proof had several small Coq normalization traps before compiling:
  - `n % d` in a helper statement parsed as a scope delimiter; the generated notation shape is `n % (d)`.
  - The divisor argument inside the recursive Coq helper normalized to `Z.pos (Pos.of_succ_nat (Z.to_nat (d - 1)))`, so the proof had to replace that constructor expression with `d`.
  - The non-dividing branch reduced to `x = x + 0`, requiring `rewrite Z.add_0_r`.
  - Some generated pure entailments were already solved by `pre_process`, so extra tactics produced `No such goal`.
- Fix action: added local helper lemmas to `coq/generated/count_divisors_proof_manual.v`:

```coq
count_divisors_upto_z_zero
count_divisors_upto_z_step_divides
count_divisors_upto_z_step_not_divides
```

and used them in the four manual witnesses.
- Result: `coqc` compiled `original/count_divisors.v`, `coq/deps/count_divisors_helper.v`, `count_divisors_goal.v`, `count_divisors_proof_auto.v`, `count_divisors_proof_manual.v`, and `count_divisors_goal_check.v` successfully. `count_divisors_proof_manual.v` contains no `Admitted.`, no manual `Axiom`, and no `Parameter`.
