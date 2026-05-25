# Verify Issues

## No annotation repair needed

- Phenomenon: the active annotated file `annotated/verify_20260422_090412_array_swap_ends.c` was identical to `input/array_swap_ends.c`.
- Trigger: the target function has no loop and no intermediate assertion point; it is an early-return branch followed by straight-line in-place array writes.
- Key C fragment:

```c
if (n < 2) {
    return;
}

t = a[0];
a[0] = a[n - 1];
a[n - 1] = t;
```

- Fix action: no `Inv`, `Assert`, `which implies`, bridge assertion, or loop-exit assertion was added.
- Result: `symexec` generated fresh Coq files from the unchanged active annotated file.

## Symbolic execution generated manual return witnesses

- Phenomenon: `symexec` succeeded but `coq/generated/array_swap_ends_proof_manual.v` contained two admitted manual obligations:

```coq
Lemma proof_of_array_swap_ends_return_wit_1 : array_swap_ends_return_wit_1.
Proof. Admitted.

Lemma proof_of_array_swap_ends_return_wit_2 : array_swap_ends_return_wit_2.
Proof. Admitted.
```

- Trigger: the postcondition is pointwise over the final array. The swap branch needs pure list reasoning over the generated double replacement:

```coq
replace_Znth (n_pre - 1) (Znth 0 l 0)
  (replace_Znth 0 (Znth (n_pre - 1) l 0) l)
```

- Localization: `coq/generated/array_swap_ends_goal.v`, definitions `array_swap_ends_return_wit_1` and `array_swap_ends_return_wit_2`.
- Fix action: added local helper lemmas in `array_swap_ends_proof_manual.v` for `replace_nth` length, `replace_Znth` length, same-index lookup, and different-index lookup. Then proved `return_wit_1` by choosing the generated double-replacement list and splitting on whether the quantified index is `0`, `n_pre - 1`, or an interior index. Proved `return_wit_2` by choosing `l`; `entailer!` discharged the no-op branch.
- Result: `array_swap_ends_proof_manual.v` compiles and contains no `Admitted.` proof and no top-level `Axiom`.

## Proof helper environment mismatch

- Phenomenon: the first manual proof compile failed before the witnesses:

```text
File ".../array_swap_ends_proof_manual.v", line 28, characters 10-28:
Error: The variable length_replace_nth was not found in the current environment.
```

- Trigger: the proof initially used a length lemma name that is not imported in this generated proof environment.
- Localization: local helper `array_swap_ends_Zlength_replace_Znth` in `coq/generated/array_swap_ends_proof_manual.v`.
- Fix action: replaced the dependency with a local induction lemma:

```coq
Lemma array_swap_ends_replace_nth_length :
  forall {A : Type} (n : nat) (x : A) (l : list A),
    length (replace_nth n x l) = length l.
```

- Result: the helper compiled, and the next compile moved to proof-script structure rather than missing imports.

## Generated proof environment induction-pattern syntax

- Phenomenon: after adding local nat-level helper lemmas, compile failed while parsing:

```text
File ".../array_swap_ends_proof_manual.v", line 27, characters 17-19:
Error: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as'
```

- Trigger: the generated proof environment with local scopes rejected the explicit `induction l as [| h t IH]` pattern.
- Localization: local helper proofs near the top of `array_swap_ends_proof_manual.v`.
- Fix action: rewrote the helper proofs to use plain `induction l` and Coq-generated names such as `IHl`.
- Result: parsing succeeded and the compile moved into `proof_of_array_swap_ends_return_wit_1`.

## `entailer!` goal order and solved-goal cleanup

- Phenomenon: after `entailer!` in `return_wit_1`, compile failed because the first bullet tried to rewrite `Zlength (replace_Znth ...)` in a goal where no such subterm existed:

```text
Error: Found no subterm matching
"Zlength (replace_Znth ?M4835 ?M4836 ?M4837)" in the current goal.
```

- Trigger: `entailer!` left the pointwise `forall i` postcondition as the first goal and the length obligation as the second goal.
- Localization: `proof_of_array_swap_ends_return_wit_1` in `array_swap_ends_proof_manual.v`.
- Fix action: used a `coqtop` probe in `logs/coqtop_probe.v` / `logs/coqtop_probe.log` to inspect the exact goal order, then reordered the bullets so the pointwise proof comes before the length proof.
- Result: `return_wit_1` compiled.

- Follow-up phenomenon: after `return_wit_1` compiled, `return_wit_2` failed with:

```text
File ".../array_swap_ends_proof_manual.v", line 142, characters 2-14:
Error: No such goal.
```

- Trigger: `pre_process; Exists l; entailer!` already solved the early-return witness completely.
- Fix action: removed the stale manual `intros i Hi` block and kept the minimal proof.
- Result: full compile replay succeeded for `array_swap_ends_goal.v`, `array_swap_ends_proof_auto.v`, `array_swap_ends_proof_manual.v`, and `array_swap_ends_goal_check.v`.

## Final verification replay

- Phenomenon: final verification needed confirmation with the full compile template, not just `proof_manual.v`.
- Trigger: verify completion requires `goal_check.v` to compile and Coq intermediates to be cleaned.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` using the documented load paths and then removed all non-`.v` files under `coq/`.
- Result: `logs/compile.log` records:

```text
compiled array_swap_ends_goal.v
compiled array_swap_ends_proof_auto.v
compiled array_swap_ends_proof_manual.v
compiled array_swap_ends_goal_check.v
compile_status=0
```

- Final state: `coq/` contains only the four generated `.v` files.
