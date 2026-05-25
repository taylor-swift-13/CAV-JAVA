# Verification Issues

## Fingerprint completion

- Phenomenon: `logs/workspace_fingerprint.json` initially had an empty `semantic_description` and empty `keywords`.
- Trigger: the workspace was bootstrapped before task-specific semantic classification.
- Localization: `output/verify_20260422_042345_array_first_peak/logs/workspace_fingerprint.json`
- Fix: read `doc/retrieval/INDEX.md` and filled a concrete description for an array scan that returns the first interior peak or `-1`. Keywords use only controlled vocabulary entries such as `search`, `while_loop`, `array`, `pointer`, `loop_invariant`, `case_split`, `range_bound`, and `empty_loop_possible`.
- Result: the fingerprint no longer has placeholder semantic fields.

## Missing loop invariant

- Phenomenon: the active annotated C initially had no loop invariant for:

```c
int i = 1;
while (i + 1 < n) {
    if (a[i] >= a[i - 1] && a[i] >= a[i + 1]) {
        return i;
    }
    i++;
}
return -1;
```

- Trigger: the postcondition needs either a successful peak index with all earlier interior positions known not to be peaks, or `-1` with all interior positions known not to be peaks.
- Localization: `annotated/verify_20260422_042345_array_first_peak.c`
- Fix: appended reasoning to `logs/annotation_reasoning.md`; added a loop-head invariant tracking `1 <= i`, unchanged `a` and `n`, `IntArray::full(a, n, l)`, and the processed-prefix fact:

```c
(forall (j: Z),
  (0 < j && j < i) =>
  (l[j] < l[j - 1] || l[j] < l[j + 1]))
```

- Result: `symexec` succeeded and generated Coq files, but the first manual proof attempt exposed an integer-safety weakness in the invariant.

## Missing integer upper bound for `i + 1`

- Phenomenon: the first generated manual proof contained `proof_of_array_first_peak_safety_wit_2`; compilation failed at `lia` with `Cannot find witness`.
- Trigger: the loop condition evaluates `i + 1`, and the invariant `i <= n + 1` was too weak to prove `i + 1 <= INT_MAX`.
- Concrete proof state:

```coq
H  : 1 <= i
H0 : i <= n_pre + 1
H2 : 0 <= n_pre
H3 : Zlength l = n_pre
============================
i + 1 <= 2147483647
```

- Fix attempted: strengthened the invariant with `n <= INT_MAX` and `i + 1 <= INT_MAX`, kept `n <= INT_MAX` in the loop-exit assertion, cleared generated files, and reran `symexec`.
- Result: `symexec` succeeded again and regenerated the manual proof obligations, but the missing bound moved to invariant initialization.

## Contract boundary: `n <= INT_MAX` is not in the input precondition

- Phenomenon: after invariant strengthening, `proof_of_array_first_peak_entail_wit_1` cannot be completed. The remaining proof obligation asks for `n_pre <= INT_MAX`.
- Trigger: the input contract only states:

```c
0 <= n &&
Zlength(l) == n &&
IntArray::full(a, n, l)
```

It does not state `n <= INT_MAX`, while the C code uses `i + 1 < n` and `i++`, whose safety needs an upper bound on the logical length.
- Localization:
  - input contract: `input/array_first_peak.c`
  - generated failing obligation: `coq/generated/array_first_peak_goal.v`, `array_first_peak_entail_wit_1`
  - proof log: `logs/proof_reasoning.md`
- Concrete proof state:

```coq
a_pre, n_pre : Z
l : list Z
H  : 0 <= n_pre
H0 : Zlength l = n_pre
============================
IntArray.full a_pre n_pre l
|-- [| n_pre <= 2147483647 |] && ...
```

- Result: Verify cannot soundly finish under the current workflow because modifying the input `Require` is a Contract-stage change. The likely contract repair is to add `n <= INT_MAX` to the precondition, as seen in nearby array examples that reason about `i + 1` or loop increments.

## Compile replay and cleanup

- Phenomenon: the compile chain stopped in `array_first_peak_proof_manual.v`; `goal_check.v` did not compile successfully under a no-error replay.
- Trigger: the remaining manual proof obligation depends on the missing contract bound above.
- Fix: recorded the blocker in `proof_reasoning.md` and this `issues.md`; cleaned non-`.v` Coq intermediate files under the current workspace.
- Result: `coq/generated/` contains only `.v` files, but verification result is `Fail` because `proof_manual.v` does not compile: the attempted `proof_of_array_first_peak_entail_wit_1` proof leaves the unprovable `n_pre <= INT_MAX` obligation open, so `goal_check.v` has not passed.

## Retry: narrowed invariant moved the blocker to preservation

- Phenomenon: removing `n <= INT_MAX` from the invariant made invariant initialization succeed, but the preservation proof for the incremented loop index got stuck.
- Trigger: after `i++`, the next loop-condition safety fact needs `((i + 1) + 1) <= INT_MAX`.
- Concrete proof state from `logs/coqtop_retry_entail_2_1_current.log`:

```coq
H0 : i + 1 < n_pre
H3 : i + 1 <= 2147483647
============================
i + 1 + 1 <= 2147483647
```

- Fix attempted: prove the semantic prefix part of the preservation witness manually by splitting `j < i` versus `j = i`; this part works, but the arithmetic side condition still needs `n_pre <= INT_MAX`.
- Result: the narrowed invariant is insufficient for preserving C-int safety across `i++`.

## Retry: pre-loop bridge assertion still cannot establish `n <= INT_MAX`

- Phenomenon: adding a pre-loop assertion with `n <= INT_MAX` regenerated `array_first_peak_entail_wit_1`, but the witness still has only the pure input contract on the left side.
- Trigger: the generated assertion-initialization VC is:

```coq
[| 0 <= n_pre |] &&
[| Zlength l = n_pre |] &&
IntArray.full a_pre n_pre l
|--
[| n_pre <= INT_MAX |] && ...
```

It does not expose a local `n` stack cell that could justify the C-int range.
- Fix attempted: keep the pre-loop assertion and rerun `symexec`, then edit `proof_manual.v` so no `Admitted.` remains and replay compilation.
- Result: final compile still fails at `proof_of_array_first_peak_entail_wit_1` with an incomplete proof. This confirms the same contract-stage gap: the formal `Require` must include `n <= INT_MAX` or an equivalent upper bound for this implementation to verify.

## Retry: conditional source-level bound avoids the false contract gap

- Phenomenon: the previous strengthened invariant made verification appear blocked by a missing contract fact `n <= INT_MAX`, but a nearby verified pattern showed that the actual safety proof can use the live stack cell for C `int n` instead of putting `n <= INT_MAX` into the invariant.
- Trigger: the active annotated C had both a pre-loop `Assert` and an `Inv` containing:

```c
n <= INT_MAX &&
i + 1 <= INT_MAX &&
```

which generated `array_first_peak_entail_wit_1` from only:

```coq
[| 0 <= n_pre |] &&
[| Zlength l = n_pre |] &&
IntArray.full a_pre n_pre l
```

to:

```coq
[| n_pre <= INT_MAX |] && ...
```

- Localization:
  - annotated file: `annotated/verify_20260422_042345_array_first_peak.c`
  - previous failing VC: `coq/generated/array_first_peak_goal.v`, old `array_first_peak_entail_wit_1`
  - failed replay: `logs/compile_retry2_20260422.log`
- Fix: removed the pre-loop assertion and replaced the invariant range with a conditional source-level bound that initializes in skip-loop cases:

```c
1 <= i && i <= n + 1 &&
(1 < n => i + 1 <= n) &&
```

The loop-exit assertion now keeps only the facts needed for the `-1` return bridge:

```c
i + 1 >= n &&
(forall (j: Z),
  (0 < j && j + 1 < n) =>
  (l[j] < l[j - 1] || l[j] < l[j + 1])) &&
IntArray::full(a, n, l)
```

- Result: reran `symexec` successfully at `2026-04-22 04:45:47 +0800` to `04:45:51 +0800`. The regenerated manual file only required `proof_of_array_first_peak_entail_wit_3` and `proof_of_array_first_peak_return_wit_2`.

## Retry: final manual proof and compile success

- Phenomenon: after the conditional-bound annotation, the remaining proof obligations were pure bridge witnesses rather than integer-bound witnesses.
- Trigger: `array_first_peak_entail_wit_3` needed to convert loop exit `i + 1 >= n_pre` plus target range `j + 1 < n_pre` into the invariant range `j < i`; `array_first_peak_return_wit_2` needed to choose the `-1` side of the postcondition disjunction.
- Fix: replaced the two generated `Admitted.` bodies in `coq/generated/array_first_peak_proof_manual.v` with:

```coq
pre_process.
entailer!.
intros j [? ?].
match goal with
| Hprefix : forall k : Z, 0 < k /\ k < i -> _ |- _ =>
    apply Hprefix
end.
lia.
```

for `proof_of_array_first_peak_entail_wit_3`, and:

```coq
pre_process.
entailer!.
Right.
entailer!.
```

for `proof_of_array_first_peak_return_wit_2`.

- Result: `logs/compile_retry2_final_20260422.log` records `goal_ok`, `proof_auto_ok`, `proof_manual_ok`, and `goal_check_ok`. `rg -n "Admitted\\.|^Axiom\\b" coq/generated/array_first_peak_proof_manual.v` returns no matches. Non-`.v` Coq intermediates were deleted after compilation, leaving only the four generated `.v` files.

## Experience update

- Phenomenon: the earlier retries repeatedly treated the absence of `n <= INT_MAX` in the contract as fatal.
- Reusable lesson: for `i + 1 < n` scan loops, prefer conditional source-level bounds in invariants, such as `(1 < n => i + 1 <= n)`, and let generated safety witnesses use the local C-int stack cell to derive `INT_MAX` facts.
- Fix: updated `experiences/general/INV.md`, section 16, with this invariant pattern.
