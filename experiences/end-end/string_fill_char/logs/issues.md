## Issue 1: active annotated C initially had no loop invariant for the in-place fill loop

- Phenomenon: `annotated/verify_20260423_023416_string_fill_char.c` initially matched the input C and had no `Inv` before:

```c
for (i = 0; i < n; ++i) {
    s[i] = c;
}
s[n] = 0;
```

- Trigger: the loop mutates `s[0..n-1]`, but the postcondition requires a logical output list `lr` where every prefix cell is `c` and `lr[n] == 0`. Without an invariant, symbolic execution would not have a stable list describing the partially updated `CharArray::full` resource across iterations.
- Localization: active annotated file `annotated/verify_20260423_023416_string_fill_char.c`, immediately before the `for` loop.
- Fix action: added an invariant carrying an existential `lr`, bounds `0 <= i <= n@pre`, unchanged parameter facts `s == s@pre`, `n == n@pre`, `c == c@pre`, list length `Zlength(lr) == n@pre + 1`, prefix semantics `(forall k, 0 <= k < i => lr[k] == c)`, suffix preservation `(forall k, i <= k < n@pre + 1 => lr[k] == l[k])`, and `CharArray::full(s, n@pre + 1, lr)`.
- Result: after clearing stale generated targets and rerunning `QualifiedCProgramming/linux-binary/symexec`, symbolic execution succeeded. `logs/qcp_run.log` ends with `Successfully finished symbolic execution` and generated fresh `string_fill_char_goal.v`, `string_fill_char_proof_auto.v`, `string_fill_char_proof_manual.v`, and `string_fill_char_goal_check.v`.

## Issue 2: manual proof placeholders for loop preservation and return witnesses

- Phenomenon: the generated manual file contained:

```coq
Lemma proof_of_string_fill_char_entail_wit_2 : string_fill_char_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_fill_char_return_wit_1 : string_fill_char_return_wit_1.
Proof. Admitted.
```

- Trigger: `symexec` correctly reduced the remaining work to pure/list obligations about `replace_Znth` preserving length, updating the selected index, and leaving other indices unchanged.
- Localization: `output/verify_20260423_023416_string_fill_char/coq/generated/string_fill_char_proof_manual.v`.
- Fix action: added local helper lemmas for `length_replace_nth`, `nth_replace_nth_same`, `nth_replace_nth_diff`, `Zlength_replace_Znth`, `Znth_replace_Znth_same`, and `Znth_replace_Znth_diff`. Proved `string_fill_char_entail_wit_2` with witness `replace_Znth i c_pre lr_2`, and proved `string_fill_char_return_wit_1` with witness `replace_Znth n_pre 0 lr_2`.
- Result: `proof_manual.v` no longer contains `Admitted.` or a newly added `Axiom`; the only `Axioms` text is the existing imported module name in `From AUXLib Require Import ... Axioms ...`.

## Issue 3: first manual proof script used the wrong generated subgoal order

- Phenomenon: the first compile of the manual proof failed in `string_fill_char_entail_wit_2` with:

```text
Hk : i + 1 <= i < n_pre + 1
Unable to unify "Znth i l 0" with "c_pre".
```

- Trigger: after `entailer!`, the first quantified subgoal was the suffix property for indices `i + 1 <= k`, but the proof script treated it as the prefix property and split on `k = i`. In that suffix subgoal, `k = i` is impossible and should be closed by arithmetic, not by the same-index replacement lemma.
- Localization: `string_fill_char_proof_manual.v`, loop-preservation proof for `proof_of_string_fill_char_entail_wit_2`.
- Fix action: reordered the proof so the first quantified subgoal proves the suffix property using `k <> i`, `Znth_replace_Znth_diff`, and the old suffix invariant. The second quantified subgoal proves the prefix property by splitting on `k = i`.
- Result: the loop-preservation witness compiled after this correction.

## Issue 4: first compile wrapper masked Coq failures because it did not use `set -e`

- Phenomenon: an early `logs/coq_compile.log` showed Coq errors but also printed later `compiled:` lines because the shell script continued after failed `coqc` commands.
- Trigger: the compile wrapper redirected all output to the log but did not enable `set -e`, so command failure did not stop the block.
- Localization: first compile attempt in `logs/coq_compile.log`; it included a proof-manual error and a follow-on `goal_check` load-path error caused by the missing manual `.vo`.
- Fix action: reran the compile template with `set -e` and treated the first `coqc` error as authoritative. After repairing the proof, reran the same template with `set -e`.
- Result: final `logs/coq_compile.log` is clean:

```text
compiled: string_fill_char_goal.v
compiled: string_fill_char_proof_auto.v
compiled: string_fill_char_proof_manual.v
compiled: string_fill_char_goal_check.v
```

## Issue 5: return witness bullet order differed from the initial proof script

- Phenomenon: after fixing the loop witness, `coqc` failed in `string_fill_char_return_wit_1` with:

```text
Error: No product even after head-reduction.
```

- Trigger: the proof script tried `intros k Hk` in the first bullet after `entailer!`, but `coqtop` showed the first return subgoal was the non-quantified terminator equality `Znth n_pre (replace_Znth n_pre 0 lr_2) 0 = 0`. The quantified prefix property was the second subgoal.
- Localization: `string_fill_char_proof_manual.v`, return proof for `proof_of_string_fill_char_return_wit_1`.
- Fix action: reordered the return proof bullets: first close the terminator equality with `Znth_replace_Znth_same`, second introduce the prefix index and use `Znth_replace_Znth_diff` plus the old prefix invariant, third prove length preservation.
- Result: final compilation of `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` succeeded.

