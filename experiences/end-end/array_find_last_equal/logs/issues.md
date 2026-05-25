# Issues: array_find_last_equal

## Fingerprint placeholder filled before verification

- Phenomenon: `logs/workspace_fingerprint.json` was still in the initialized state, with an empty `semantic_description` and `{}` for `keywords`.
- Trigger: the verify workspace had been created but no prior agent had completed the early fingerprint step.
- Fix action: read `doc/retrieval/INDEX.md` and filled the fingerprint with a semantic description of the left-to-right last-match array scan. The keyword keys and values were chosen only from the controlled vocabulary: `algorithm_family=search`, `control_flow=[for_loop, if]`, `data_shape=array`, `semantic_intent=preserve_input`, `proof_pattern=[loop_invariant, case_split, range_bound, heap_reasoning]`, `numeric_properties=[nonnegative_input, int_range]`, `edge_case_behavior=empty_loop_possible`, and finally `verification_status=goal_check_passed`.
- Result: the fingerprint is no longer a placeholder and can be used for later retrieval.

## Initial disjunctive invariant caused a loop invariant assertion-count mismatch

- Phenomenon: the first `symexec` run failed at the loop invariant with:

```text
fatal error: The number of now assertions and loop inv pre assertions does not match. in .../annotated/verify_20260422_040059_array_find_last_equal.c:37:4
```

- Trigger: the first invariant modeled the `ans` state using a top-level disjunction:

```c
((ans == -1 &&
  (forall (j: Z), (0 <= j && j < i) => l[j] != k)) ||
 (0 <= ans && ans < i &&
  l[ans] == k &&
  (forall (j: Z), (ans < j && j < i) => l[j] != k)))
```

- Root cause: semantically this was the right last-match prefix invariant, but the frontend split it into multiple assertion cases at the loop boundary while the symbolic pre-state was a single assertion. That produced a structural mismatch before Coq proof generation.
- Fix action: rewrote the invariant and loop-exit assertion into a single conjunctive assertion using guarded implications:

```c
-1 <= ans && ans < i &&
(ans == -1 => (forall (j: Z), (0 <= j && j < i) => l[j] != k)) &&
(0 <= ans => (l[ans] == k &&
              (forall (j: Z), (ans < j && j < i) => l[j] != k))) &&
IntArray::full(a, n, l)
```

- Result: rerunning `QualifiedCProgramming/linux-binary/symexec` with the canonical explicit output paths succeeded and regenerated `array_find_last_equal_goal.v`, `array_find_last_equal_proof_auto.v`, `array_find_last_equal_proof_manual.v`, and `array_find_last_equal_goal_check.v`.

## Manual proof obligations required proof-state-driven refinement

- Phenomenon: successful `symexec` generated four admitted manual lemmas in `coq/generated/array_find_last_equal_proof_manual.v`:

```coq
proof_of_array_find_last_equal_entail_wit_1
proof_of_array_find_last_equal_entail_wit_2_1
proof_of_array_find_last_equal_entail_wit_3
proof_of_array_find_last_equal_return_wit_1
```

- Fix action: replaced all four `Admitted.` proofs with completed scripts. The first two witnesses were solved by `unfold; intros; entailer!`. `entail_wit_3` needed explicit use of the two invariant implications after `entailer!` exposed `i >= n_pre` and `i <= n_pre`; the proof derives `i = n_pre` inside each remaining subgoal and applies the saved implication hypotheses. `return_wit_1` needed `pre_process` before branching on `ans`, then assertion-level `Right` for `ans = -1` and assertion-level `Left` for `0 <= ans`.
- Representative final return proof:

```coq
Lemma proof_of_array_find_last_equal_return_wit_1 : array_find_last_equal_return_wit_1.
Proof.
  unfold array_find_last_equal_return_wit_1.
  pre_process.
  destruct (Z.eq_dec ans (-1)) as [Hans_eq | Hans_neq].
  - Right.
    entailer!.
  - assert (Hans_nonneg : 0 <= ans) by lia.
    destruct (H4 Hans_nonneg) as [Hans_val Hlast].
    Left.
    entailer!.
Qed.
```

- Result: `array_find_last_equal_proof_manual.v` now contains no `Admitted.` and no local `Axiom`.

## Compile and cleanup

- Phenomenon: verification is not complete after `symexec`; `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` must compile with the full load-path template.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with `_CoqProject`-equivalent base `-R` flags plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260422_040059_array_find_last_equal`.
- Relevant compile log:

```text
compile array_find_last_equal_goal.v
compile array_find_last_equal_proof_auto.v
compile array_find_last_equal_proof_manual.v
compile array_find_last_equal_goal_check.v
compile_status: 0
```

- Result: full compile passed, then non-`.v` Coq build artifacts under the current workspace `coq/` directory were deleted. Only generated `.v` files remain.
