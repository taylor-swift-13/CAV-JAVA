# Proof Reasoning

## 2026-04-23 05:43:36 +0800 - First manual proof plan after successful symexec

Fresh `symexec` succeeded on the active annotated C file and generated four manual obligations in `coq/generated/ways_to_reach_proof_manual.v`:

```coq
Lemma proof_of_ways_to_reach_safety_wit_6 : ways_to_reach_safety_wit_6.
Lemma proof_of_ways_to_reach_entail_wit_1 : ways_to_reach_entail_wit_1.
Lemma proof_of_ways_to_reach_entail_wit_2 : ways_to_reach_entail_wit_2.
Lemma proof_of_ways_to_reach_return_wit_1 : ways_to_reach_return_wit_1.
```

The current generated file has each of these as `Proof. Admitted.`, which must be replaced with real proofs. The corresponding VCs in `ways_to_reach_goal.v` show no missing heap resources. The hard parts are pure recurrence and integer bounds:

```coq
Definition ways_to_reach_safety_wit_6 :=
forall (n_pre b a i: Z),
  [| i <= n_pre |] && [| 1 <= n_pre |] && [| n_pre <= 45 |] &&
  [| 2 <= i |] && [| i <= n_pre + 1 |] &&
  [| a = ways_to_reach_z (i - 2) |] &&
  [| b = ways_to_reach_z (i - 1) |] && ...
|-- [| a + b <= INT_MAX |] && [| INT_MIN <= a + b |].
```

and invariant preservation:

```coq
[| b = ways_to_reach_z (i - 1) |] &&
[| a = ways_to_reach_z (i - 2) |]
|-- [| b = ways_to_reach_z ((i + 1) - 2) |] &&
    [| a + b = ways_to_reach_z ((i + 1) - 1) |].
```

The contract bound `n_pre <= 45` and loop facts imply `2 <= i <= 45` in loop-body witnesses. The imported Coq definition is structurally recursive through `Z.to_nat`, so `vm_compute` can compute each bounded case. I will add two local tactics:

```coq
Ltac zcase x n := destruct (Z.eq_dec x n) as [Heq | Hneq]; ...
Ltac split_small_range x := zcase x 0; ...; zcase x 45; lia.
```

For `safety_wit_6`, after `pre_process; entailer!`, substitute `a` and `b` from the invariant equalities and run `split_small_range i`. For `entail_wit_2`, use the same substitutions and bounded split on `i`; each concrete recurrence step reduces by `vm_compute`. `entail_wit_1` and `return_wit_1` only need `pre_process`/`entailer!` plus computation or arithmetic for the initial values and the `n_pre = 0` branch.

## 2026-04-23 05:44:31 +0800 - Fix overlong tactic in `entail_wit_1`

The first compile attempt reached `ways_to_reach_proof_manual.v` and failed at line 49:

```text
Error: No such goal.
```

The failing proof fragment was:

```coq
Lemma proof_of_ways_to_reach_entail_wit_1 : ways_to_reach_entail_wit_1.
Proof.
  pre_process.
  entailer!; vm_compute; repeat split; try congruence; lia.
Qed.
```

This error means `entailer!` had already solved the goal and the following `vm_compute` branch was applied when no subgoal remained. This is not an annotation issue and not a missing recurrence lemma. The fix is to keep the proof at the smaller stable skeleton:

```coq
Proof.
  pre_process.
Qed.
```

After this change I will rerun the full compile command with `set -e`/`pipefail` so a `coqc` failure stops the script and the final compile status reflects the real result.

## 2026-04-23 05:46:50 +0800 - Replace broad computation with recurrence lemmas

The second compile attempt got through `goal.v` and `proof_auto.v` but then spent over a minute compiling `ways_to_reach_proof_manual.v` with no output. The running process was:

```text
coqc ... ways_to_reach_proof_manual.v
```

The likely cause is the broad `split_small_range` tactic invoking `vm_compute` inside the full witness proof context for both the safety and preservation witnesses. The imported `ways_to_reach_z` is a structurally recursive pair function, so proving the recurrence step by full computation in every case is unnecessarily heavy.

I will replace the preservation proof with local helper lemmas over the Coq model:

```coq
Lemma ways_to_reach_nat_step : forall n,
  ways_to_reach_nat (S (S n)) =
  ways_to_reach_nat (S n) + ways_to_reach_nat n.

Lemma ways_to_reach_z_step : forall z,
  2 <= z ->
  ways_to_reach_z z = ways_to_reach_z (z - 1) + ways_to_reach_z (z - 2).
```

The helper unfolds `ways_to_reach_pair` once and uses `Z2Nat.inj_add` to bridge from `z`, `z - 1`, and `z - 2` to the corresponding natural indices. Then `entail_wit_2` can rewrite by the recurrence instead of case-splitting through all 46 possible values.

For the C integer overflow witness, I will keep a small bounded-computation lemma:

```coq
Lemma ways_to_reach_z_bound_45 : forall z,
  0 <= z <= 45 -> 0 <= ways_to_reach_z z <= INT_MAX.
```

This confines `vm_compute` to a pure arithmetic helper and lets `safety_wit_6` rewrite `a + b` to `ways_to_reach_z i` via the recurrence before applying the bound.

## 2026-04-23 05:49:02 +0800 - Normalize recurrence sum order in safety witness

Compiling `ways_to_reach_proof_manual.v` after adding the recurrence helpers failed at `proof_of_ways_to_reach_safety_wit_6`:

```text
line 76: Error: Found no subterm matching
"ways_to_reach_z (?M - 1) + ways_to_reach_z (?M - 2)"
in the current goal.
```

After substituting the invariant equalities, the safety goal contains the C expression in source order:

```coq
ways_to_reach_z (i - 2) + ways_to_reach_z (i - 1)
```

but `ways_to_reach_z_step` rewrites:

```coq
ways_to_reach_z i =
ways_to_reach_z (i - 1) + ways_to_reach_z (i - 2)
```

The fix is a local `replace` using commutativity/`lia` before the reverse rewrite, then apply the bounded lemma for `ways_to_reach_z i`.

## 2026-04-23 05:49:35 +0800 - Add spatial cleanup bullet for `entail_wit_2`

After fixing the recurrence sum order, `proof_of_ways_to_reach_entail_wit_2` still failed with `Proof is not complete`. A `coqtop` probe after the two pure bullets showed the remaining goal:

```coq
n_pre, i : Z
H : i <= n_pre
H0 : 1 <= n_pre
H1 : n_pre <= 45
H2 : 2 <= i
H3 : i <= n_pre + 1
...
============================
&( "c") # Int |-> (ways_to_reach_z (i - 2) + ways_to_reach_z (i - 1))
|-- &( "c") # Int |->_
```

This is the spatial part of consuming the local `c` value into an undefined local slot in the loop invariant. It is not related to the recurrence proof. The fix is to add a final bullet:

```coq
apply poly_store_poly_undef_store.
```

before the final pure proof; this is the same common strategy lemma used by the project to prove `poly_store ty p v |-- poly_undef_store ty p`. The working order is:

```coq
sep_apply (poly_store_poly_undef_store (&( "c")) FET_int (a + b)).
entailer!; subst a; subst b.
```

At that point `coqtop` shows only the two pure recurrence goals:

```coq
a + b = ways_to_reach_z (i + 1 - 1)
b = ways_to_reach_z (i + 1 - 2)
```

These are then solved by rewriting the first with `ways_to_reach_z_step` and simplifying the second index arithmetically.
