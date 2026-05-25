# Proof Reasoning

## Manual witnesses after first successful symexec

- Current generated manual file: `output/verify_20260422_131939_climb_stairs/coq/generated/climb_stairs_proof_manual.v`.
- `symexec` succeeded on the latest annotated C file, but the generated manual file contains four `Admitted.` obligations:

```coq
Lemma proof_of_climb_stairs_safety_wit_7 : climb_stairs_safety_wit_7.
Proof. Admitted.

Lemma proof_of_climb_stairs_entail_wit_1 : climb_stairs_entail_wit_1.
Proof. Admitted.

Lemma proof_of_climb_stairs_entail_wit_2 : climb_stairs_entail_wit_2.
Proof. Admitted.

Lemma proof_of_climb_stairs_return_wit_1 : climb_stairs_return_wit_1.
Proof. Admitted.
```

- The obligations are pure scalar facts:
  - `safety_wit_7`: under loop-head facts `2 <= i <= n_pre <= 45`, `prev2 = climb_stairs_z(i - 2)`, and `prev1 = climb_stairs_z(i - 1)`, prove `prev1 + prev2` is inside C `int` range before `cur = prev1 + prev2`.
  - `entail_wit_1`: prove the invariant initialization at `i = 2`, including `1 = climb_stairs_z(0)` and `1 = climb_stairs_z(1)`.
  - `entail_wit_2`: prove invariant preservation, especially the recurrence step `climb_stairs_z(i - 1) + climb_stairs_z(i - 2) = climb_stairs_z(i)`.
  - `return_wit_1`: prove the early branch `0 <= n_pre <= 1` returns `1 = climb_stairs_z n_pre`.
- Available facts are bounded: `n_pre <= 45` and loop preservation adds `i <= n_pre`, so the hard arithmetic can be made stable by explicitly case-splitting the finite range and normalizing `climb_stairs_z` with `vm_compute`. This is preferable here to introducing a general Fibonacci recurrence and monotonicity development, because the C contract intentionally bounds the input to `45` as the overflow guard.
- Planned proof shape:

```coq
Ltac split_small_range x :=
  assert (x = 0 \/ x = 1 \/ ... \/ x = 45) by lia;
  repeat destruct disjunctions; subst; vm_compute; lia.

Proof.
  pre_process.
  entailer!.
  split_small_range i.
Qed.
```

- This proof uses only generated facts and computation over the existing `climb_stairs_z` definition from `original/climb_stairs.v`; it adds no `Axiom` and leaves no `Admitted.` in `proof_manual.v`.

## Compile blocker in original Coq input and workspace-local dependency

- First compile attempt used the documented template and failed before checking any generated witness:

```text
File ".../output/verify_20260422_131939_climb_stairs/original/climb_stairs.v", line 5, characters 0-147:
Error:
Recursive definition of climb_stairs_nat is ill-formed.
...
Recursive call to climb_stairs_nat has principal argument equal to
"S k" instead of one of the following variables: "n0"
"k".
```

- The blocked definition is the contract-provided optional Coq file copied into `original/climb_stairs.v`:

```coq
Fixpoint climb_stairs_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S O => 1
  | S (S k) => climb_stairs_nat (S k) + climb_stairs_nat k
  end.
```

- Coq rejects the recursive call on `S k` because it is not accepted as structurally decreasing in that pattern. I did not edit `input/climb_stairs.v` or `original/climb_stairs.v`. To keep verification inside the workspace and unblock compilation, I added `coq/deps/climb_stairs.v` with the same recurrence written as a nested match:

```coq
Fixpoint climb_stairs_nat (n : nat) : Z :=
  match n with
  | O => 1
  | S n' =>
      match n' with
      | O => 1
      | S k => climb_stairs_nat n' + climb_stairs_nat k
      end
  end.
```

- Next compile attempt should compile `coq/deps/climb_stairs.v` first and place `-Q "$DEPS" ""` before the generated path so unqualified `Require Import climb_stairs` resolves to the workspace-local structurally accepted definition. This is a dependency workaround for an invalid optional Coq input, not a change to the C annotation or generated VCs.

## Replacing slow finite disjunction tactic

- The first compile with the workspace-local dependency reached `coq/generated/climb_stairs_proof_manual.v` but stayed CPU-bound for roughly 50 seconds. `ps` showed the active process was:

```text
coqc ... /output/verify_20260422_131939_climb_stairs/coq/generated/climb_stairs_proof_manual.v
```

- The likely cause was the initial `split_small_range` tactic, which built one large 46-way disjunction and then destructed it. That creates a large nested proof term before any branch closes:

```coq
assert (x = 0 \/ x = 1 \/ ... \/ x = 45) by lia;
repeat match goal with H : _ \/ _ |- _ => destruct H as [H | H] end;
subst; vm_compute; lia.
```

- I replaced it with a linear `Z.eq_dec` tactic. Each successful branch substitutes, computes `climb_stairs_z`, and closes immediately; the final branch is impossible by `lia` from the bounded hypotheses:

```coq
Ltac zcase x n :=
  destruct (Z.eq_dec x n) as [Heq | Hneq];
  [ subst; vm_compute; lia | idtac ].

Ltac split_small_range x :=
  zcase x 0; zcase x 1; ...; zcase x 45; lia.
```

- This keeps the same proof idea but avoids the expensive up-front disjunction term.

## Safety witness pure goals need scalar substitution before range split

- After the faster tactic change, `coqc` failed at `proof_of_climb_stairs_safety_wit_7` with:

```text
Error: Tactic failure: Cannot find witness.
```

- Inspecting the proof state after `pre_process; entailer!.` showed two pure arithmetic subgoals still expressed through the program variables:

```coq
n_pre, cur, prev1, prev2, i : Z
H4 : prev2 = climb_stairs_z (i - 2)
H5 : prev1 = climb_stairs_z (i - 1)
============================
-2147483648 <= prev1 + prev2

goal 2 is:
prev1 + prev2 <= 2147483647
```

- The range split on `i` only computes `climb_stairs_z` after `prev1` and `prev2` are substituted with `H5` and `H4`. I updated the safety and preservation witnesses to run:

```coq
entailer!; subst prev1; subst prev2; split_small_range i.
```

- This keeps the proof tied directly to the invariant facts `prev2 = climb_stairs_z(i - 2)` and `prev1 = climb_stairs_z(i - 1)`.

## Computed comparison goals need congruence after vm_compute

- After adding scalar substitution, the next compile still failed in `safety_wit_7`. Inspecting an `i = 2` branch showed that `vm_compute` reduced a pure lower-bound arithmetic goal to a comparison-discrimination shape:

```coq
============================
Lt = Gt -> False
```

- `lia` does not close this already-computed comparison contradiction. I changed each successful finite case branch from:

```coq
subst; vm_compute; lia
```

to:

```coq
subst; vm_compute; try congruence; lia
```

- The `congruence` step closes computed impossible equalities such as `Lt = Gt`; remaining numeric branches still fall through to `lia`.
