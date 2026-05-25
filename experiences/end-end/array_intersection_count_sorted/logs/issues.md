## 2026-04-22 05:25 CST - Active annotated copy initially had no loop invariant

- Phenomenon: the active annotated C file `annotated/verify_20260422_051342_array_intersection_count_sorted.c` initially copied the input C and had no `Inv` before the two-pointer loop:

```c
int i = 0;
int j = 0;
int count = 0;
while (i < n && j < m) {
    if (a[i] == b[j]) {
        count++;
        i++;
        j++;
    } else if (a[i] < b[j]) {
        i++;
    } else {
        j++;
    }
}
```

- Trigger: without a loop-head invariant, symbolic execution would not preserve the relationship between `count`, the consumed prefixes, the remaining suffixes, and the recursive Coq spec `array_intersection_count_sorted_spec`.
- Fix: added a loop invariant in the active annotated file only. The key semantic clause is:

```c
count + array_intersection_count_sorted_spec(sublist(i, n, la), sublist(j, m, lb)) ==
  array_intersection_count_sorted_spec(la, lb)
```

with bounds for `i`, `j`, and `count`, unchanged parameter equalities, sortedness facts, and both `IntArray::full` predicates.
- Result: after clearing stale generated files and rerunning `QualifiedCProgramming/linux-binary/symexec` with explicit `--input-file=...`, `--goal-file=...`, `--proof-auto-file=...`, `--proof-manual-file=...`, and `--goal-check-file=...`, symbolic execution succeeded. `logs/qcp_run.log` ends with:

```text
Successfully finished symbolic execution
symexec_end=2026-04-22T05:16:06+08:00
symexec_elapsed=6
symexec_status=0
```

## 2026-04-22 05:25 CST - Manual proof obligations required suffix-step helpers

- Phenomenon: fresh `symexec` generated six `Admitted.` placeholders in `coq/generated/array_intersection_count_sorted_proof_manual.v`:

```coq
proof_of_array_intersection_count_sorted_entail_wit_1
proof_of_array_intersection_count_sorted_entail_wit_2_1
proof_of_array_intersection_count_sorted_entail_wit_2_2
proof_of_array_intersection_count_sorted_entail_wit_2_3
proof_of_array_intersection_count_sorted_return_wit_1
proof_of_array_intersection_count_sorted_return_wit_2
```

- Trigger: the generated VCs contained the right suffix invariant, but Coq still needed explicit facts connecting nonempty `sublist` suffixes to the recursive branches of `array_intersection_count_sorted_spec`.
- Fix: added local helper lemmas in `proof_manual.v`:

```coq
array_intersection_sublist_cons
array_intersection_spec_nil_r
array_intersection_step_eq
array_intersection_step_lt
array_intersection_step_gt
```

The branch witnesses use the step helpers; the return witnesses rewrite the exhausted suffix to `nil` and use the invariant equality to conclude `count = array_intersection_count_sorted_spec la lb`.
- Result: `coq/generated/array_intersection_count_sorted_proof_manual.v` compiles and `rg "Admitted\\.|\\bAxiom\\b" ..._proof_manual.v` returns no matches.

## 2026-04-22 05:25 CST - Helper proof needed explicit length bridge for `sublist_split`

- Phenomenon: the first manual proof compile failed at the local helper:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 30, characters 46-49:
Error: Tactic failure:  Cannot find witness.
```

The failing code was:

```coq
rewrite (sublist_split lo hi (lo + 1) l) by lia.
```

- Trigger: `array_intersection_sublist_cons` had `hi <= Zlength l`, while `sublist_split` expects its upper bound as `hi <= Z.of_nat (length l)`.
- Fix: added an explicit bridge:

```coq
assert (Hhi_len : hi <= Z.of_nat (length l)).
{
  rewrite <- Zlength_correct.
  exact Hhi.
}
```

and used `rewrite <- Zlength_correct` for `sublist_single` side conditions.
- Result: the helper advanced to the next proof script issue.

## 2026-04-22 05:25 CST - Loose comparison proof script produced `No such goal`

- Phenomenon: after the length bridge, compile failed in `array_intersection_step_eq`:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 65, characters 2-14:
Error: No such goal.
```

- Trigger: the script used:

```coq
destruct (Z.eq_dec (Znth i la 0) (Znth j lb 0)); try lia.
reflexivity.
```

In one branch, `lia` solved the remaining reflexive goal, so the following `reflexivity` had no goal.
- Fix: rewrote the comparison helpers with explicit branches:

```coq
destruct (Z.eq_dec ... ) as [Heq | Hneq].
- reflexivity.
- lia.
```

and similarly split `Z.ltb_spec0` in the less-than and greater-than helpers.
- Result: comparison helper lemmas compiled.

## 2026-04-22 05:25 CST - Return witnesses required targeted empty-suffix rewrites

- Phenomenon: return proof attempts first failed due unstable hypothesis numbering and then failed with:

```text
File ".../array_intersection_count_sorted_proof_manual.v", line 174, characters 32-35:
Error: Tactic failure:  Cannot find witness.
```

- Trigger: `rewrite sublist_nil in H16 by lia` tried to rewrite the wrong sublist occurrence. In `return_wit_1`, the first suffix `sublist i_3 n_pre la` is not empty because the branch still has `i_3 < n_pre`; only the second suffix `sublist m_pre m_pre lb` is empty. In `return_wit_2`, only `sublist n_pre n_pre la` is empty.
- Fix: inspected the proof state with `coqtop` and then targeted the exhausted suffix explicitly:

```coq
replace (sublist m_pre m_pre lb) with (@nil Z) in H16
  by (rewrite sublist_nil by lia; reflexivity).
rewrite array_intersection_spec_nil_r in H16.
```

and for the other return branch:

```coq
replace (sublist n_pre n_pre la) with (@nil Z) in H15
  by (rewrite sublist_nil by lia; reflexivity).
simpl in H15.
```

- Result: both return witnesses compiled; the full Coq chain from `original/array_intersection_count_sorted.v` through `array_intersection_count_sorted_goal_check.v` compiled successfully.

## 2026-04-22 05:25 CST - Final compile and cleanup

- Phenomenon: verification is not complete after `symexec`; the generated Coq modules must compile and non-`.v` Coq artifacts must be removed.
- Fix: compiled, in order, `original/array_intersection_count_sorted.v`, `array_intersection_count_sorted_goal.v`, `array_intersection_count_sorted_proof_auto.v`, `array_intersection_count_sorted_proof_manual.v`, and `array_intersection_count_sorted_goal_check.v`. Because this workspace's generated files use unqualified `Require Import array_intersection_count_sorted_goal`, the generated directory was compiled with `-Q "$GEN" ""` and the original spec with `-Q "$ORIG" ""`.
- Result: all compile logs are empty, indicating success. After compile success, deleted all non-`.v` files under `coq/`; the only remaining Coq files are:

```text
coq/generated/array_intersection_count_sorted_goal.v
coq/generated/array_intersection_count_sorted_goal_check.v
coq/generated/array_intersection_count_sorted_proof_auto.v
coq/generated/array_intersection_count_sorted_proof_manual.v
```
