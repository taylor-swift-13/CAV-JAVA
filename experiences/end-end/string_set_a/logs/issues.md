## Issue 1: active annotated C initially had no loop invariant for the in-place string fill loop

- Phenomenon: `annotated/verify_20260423_041814_string_set_a.c` initially matched the input C and had no `Inv` before the mutating loop:

```c
for (i = 0; i < n; ++i) {
    s[i] = 97;
}
s[n] = 0;
```

- Trigger: the loop writes `s[0..n-1]`, while the postcondition requires an existential logical list `lr` with `Zlength(lr) == n + 1`, every prefix cell equal to `97`, `lr[n] == 0`, and `CharArray::full(s, n + 1, lr)`. Without an invariant, symbolic execution has no stable logical list describing the partially updated `CharArray::full` resource across iterations.
- Localization: active annotated file `annotated/verify_20260423_041814_string_set_a.c`, immediately before the `for` loop.
- Fix action: added an invariant carrying existential `lr`, bounds `0 <= i && i <= n@pre`, unchanged parameter facts `s == s@pre` and `n == n@pre`, list length `Zlength(lr) == n@pre + 1`, prefix semantics `(forall k, 0 <= k && k < i => lr[k] == 97)`, suffix preservation `(forall k, i <= k && k < n@pre + 1 => lr[k] == l[k])`, and `CharArray::full(s, n@pre + 1, lr)`.

Key fixed annotation:

```c
/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      s == s@pre &&
      n == n@pre &&
      Zlength(lr) == n@pre + 1 &&
      (forall (k: Z), (0 <= k && k < i) => lr[k] == 97) &&
      (forall (k: Z), (i <= k && k < n@pre + 1) => lr[k] == l[k]) &&
      CharArray::full(s, n@pre + 1, lr)
*/
for (i = 0; i < n; ++i) {
    s[i] = 97;
}
```

- Result: after clearing stale generated targets and rerunning `QualifiedCProgramming/linux-binary/symexec` with explicit `--goal-file=...`, `--proof-auto-file=...`, `--proof-manual-file=...`, `--goal-check-file=...`, `--input-file=annotated/verify_20260423_041814_string_set_a.c`, `--coq-logic-path=SimpleC.EE.CAV.verify_20260423_041814_string_set_a`, `-slp QualifiedCProgramming/QCP_examples/ SimpleC.EE`, and `--no-exec-info`, symbolic execution succeeded. `logs/qcp_run.log` ends with `Successfully finished symbolic execution` and generated fresh `string_set_a_goal.v`, `string_set_a_proof_auto.v`, `string_set_a_proof_manual.v`, and `string_set_a_goal_check.v`.

## Issue 2: generated manual proof contained placeholders for loop preservation and return witnesses

- Phenomenon: `output/verify_20260423_041814_string_set_a/coq/generated/string_set_a_proof_manual.v` initially contained:

```coq
Lemma proof_of_string_set_a_entail_wit_2 : string_set_a_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_set_a_return_wit_1 : string_set_a_return_wit_1.
Proof. Admitted.
```

- Trigger: `symexec` correctly reduced the remaining work to pure/list facts about `replace_Znth`: preserving `Zlength`, returning the newly written value at the updated index, and preserving all other indices.
- Localization: manual witness definitions in `string_set_a_goal.v`:

```coq
Definition string_set_a_entail_wit_2 := ... CharArray.full s_pre (n_pre + 1) (replace_Znth i 97 lr_2) |-- EX lr, ...
Definition string_set_a_return_wit_1 := ... CharArray.full s_pre (n_pre + 1) (replace_Znth n_pre 0 lr_2) |-- EX lr, ...
```

- Fix action: added local helper lemmas `length_replace_nth`, `nth_replace_nth_same`, `nth_replace_nth_diff`, `Zlength_replace_Znth`, `Znth_replace_Znth_same`, and `Znth_replace_Znth_diff`. Proved `string_set_a_entail_wit_2` with witness `replace_Znth i 97 lr_2`; proved `string_set_a_return_wit_1` with witness `replace_Znth n_pre 0 lr_2` after deriving `i_2 = n_pre` by `lia`.
- Result: `string_set_a_proof_manual.v` compiles and contains no `Admitted.`. The only `Axioms` text is the existing imported module name in:

```coq
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
```

No new `Axiom` was added.

## Issue 3: proof subgoal order required handling suffix before prefix

- Phenomenon: after `entailer!` in the loop preservation witness, the first quantified goal is the suffix preservation obligation for indices `i + 1 <= k < n_pre + 1`, not the prefix obligation.
- Trigger: QCP generated the target order as suffix property, prefix property, and length property. Treating the first quantified goal as the prefix case would wrongly split on `k = i`; but in the suffix goal `k = i` is impossible and should be closed by arithmetic.
- Localization: `proof_of_string_set_a_entail_wit_2` in `string_set_a_proof_manual.v`.
- Fix action: first proved the suffix subgoal using `Znth_replace_Znth_diff` and the old suffix invariant:

```coq
- intros k Hk.
  assert (Hneq : k <> i) by lia.
  rewrite Znth_replace_Znth_diff by lia.
  match goal with
  | Hsuffix : forall k : Z, (((i <= k) /\ (k < n_pre + 1)) -> Znth k lr_2 0 = Znth k l 0) |- _ =>
      apply Hsuffix; lia
  end.
```

Then proved the prefix subgoal by case splitting on `k = i`, using `Znth_replace_Znth_same` for the updated cell and the old prefix invariant for all earlier cells.
- Result: the manual proof compiled successfully.

## Issue 4: compile success must be checked with `goal_check.v`, then intermediates cleaned

- Phenomenon: compiling only `proof_manual.v` would not establish the full generated VC bundle is accepted. The workflow requires `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all to compile with the current workspace logic path.
- Trigger: final validation step after replacing the manual proof placeholders.
- Localization: compile log `output/verify_20260423_041814_string_set_a/logs/coq_compile.log`.
- Fix action: ran the documented compile template from `QualifiedCProgramming/SeparationLogic` with `set -e`, using base `-R` load paths and extra `-Q "$ORIG" "" -R "$GEN" SimpleC.EE.CAV.verify_20260423_041814_string_set_a`.
- Result: `logs/coq_compile.log` is clean:

```text
compiled: string_set_a_goal.v
compiled: string_set_a_proof_auto.v
compiled: string_set_a_proof_manual.v
compiled: string_set_a_goal_check.v
```

After compilation, removed all non-`.v` files under `output/verify_20260423_041814_string_set_a/coq/`. `input/` had no non-`.c`/non-`.v` intermediate files to remove.
