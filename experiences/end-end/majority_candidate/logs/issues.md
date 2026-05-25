# Issues

## 1. `majority_candidate_acc` used in invariant but not declared to annotation frontend

Phenomenon: the first `symexec` run failed before VC generation:

```text
fatal error: Use of undeclared identifier `majority_candidate_acc' in annotated/verify_20260422_190218_majority_candidate.c:32:4
```

Trigger: the loop invariant used the Coq helper `majority_candidate_acc`:

```c
majority_candidate_acc(candidate, count, sublist(i, n, l)) == majority_candidate_spec(l)
```

The input C only declared:

```c
/*@ Extern Coq (majority_candidate_spec : list Z -> Z) */
```

Even though `input/majority_candidate.v` defines `majority_candidate_acc` and the C file imports `majority_candidate`, the annotation frontend still needs a matching `Extern Coq` declaration for symbols used directly in C annotations.

Fix: updated only the active annotated copy to expose the existing helper:

```c
/*@ Extern Coq (majority_candidate_acc : Z -> Z -> list Z -> Z)
               (majority_candidate_spec : list Z -> Z) */
```

Result: the next `symexec` run progressed past parsing the invariant.

## 2. Loop-exit assertion dropped live local `count`

Phenomenon: after the `Extern Coq` fix, `symexec` failed at the exit assertion:

```text
fatal error: Error: Fail to Remove Memory Permission of count:104 in .../annotated/verify_20260422_190218_majority_candidate.c:51:4
```

Trigger: the first exit assertion intentionally kept only facts needed by the return value:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      candidate == majority_candidate_spec(l) &&
      IntArray::full(a, n, l)
*/
```

At that program point, the local variable `count` was still live, but the assertion did not mention it, so the frontend tried to remove its local permission too early.

Fix: kept a harmless pure bound for `count` in the exit assertion:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      0 <= count && count <= n &&
      candidate == majority_candidate_spec(l) &&
      IntArray::full(a, n, l)
*/
```

Result: `symexec` completed successfully and generated fresh `majority_candidate_goal.v`, `majority_candidate_proof_auto.v`, `majority_candidate_proof_manual.v`, and `majority_candidate_goal_check.v`.

## 3. Manual proof hypothesis numbering differed by witness

Phenomenon: the first manual proof compile failed in `proof_of_majority_candidate_entail_wit_2_1`:

```text
Error: Found no subterm matching
"majority_candidate_acc candidate count (sublist i n_pre l)" in H6.
```

Trigger: after `pre_process`, the accumulator invariant equality was not always assigned the same hypothesis number.  In `entail_wit_2_1`, `coqtop` showed:

```coq
H5 :
  majority_candidate_acc candidate count (sublist i n_pre l) =
  majority_candidate_spec l
H6 : 1 <= n_pre
```

In `entail_wit_2_2` and `entail_wit_2_3`, the corresponding equality was `H6`.  In `entail_wit_3`, it was `H4`.

Fix: adjusted the proof scripts to rewrite the helper lemma into the actual accumulator-equality hypothesis for each witness:

```coq
rewrite Hacc in H5 by lia.  (* entail_wit_2_1 *)
rewrite Hacc in H6 by lia.  (* entail_wit_2_2 / 2_3 *)
replace (sublist n_pre n_pre l) with (@nil Z) in H4.  (* entail_wit_3 *)
```

Result: after these corrections, the full Coq compile sequence passed through `majority_candidate_goal_check.v`.
