## 2026-04-22 manual witnesses after successful symexec

Fresh `symexec` succeeded for `annotated/verify_20260422_092628_binary_search_first.c` and generated:

```text
coq/generated/binary_search_first_goal.v
coq/generated/binary_search_first_proof_auto.v
coq/generated/binary_search_first_proof_manual.v
coq/generated/binary_search_first_goal_check.v
```

The generated manual file contains six admitted obligations:

```coq
proof_of_binary_search_first_safety_wit_2
proof_of_binary_search_first_entail_wit_1
proof_of_binary_search_first_entail_wit_2
proof_of_binary_search_first_entail_wit_3_1
proof_of_binary_search_first_entail_wit_3_2
proof_of_binary_search_first_return_wit_2
```

The current proof context is a lower-bound binary search. The key generated obligations are:

```coq
Definition binary_search_first_entail_wit_2 := ... |--
  [| 0 <= left + (right - left) ÷ 2 |] &&
  [| left + (right - left) ÷ 2 < n_pre |] &&
  [| left <= left + (right - left) ÷ 2 |] &&
  [| left + (right - left) ÷ 2 < right |] && ...

Definition binary_search_first_entail_wit_3_1 := ... Znth mid l 0 >= target_pre ... |--
  ... [| forall i, mid <= i /\ i < n_pre -> target_pre <= Znth i l 0 |] ...

Definition binary_search_first_entail_wit_3_2 := ... Znth mid l 0 < target_pre ... |--
  ... [| forall i, 0 <= i /\ i < mid + 1 -> Znth i l 0 < target_pre |] ...

Definition binary_search_first_return_wit_2 := ... Znth left l 0 <> target_pre ... left >= right ... left <= right ... |--
  return -1 postcondition
```

The nearest reusable proof pattern is `examples/binary_search/coq/generated/binary_search_proof_manual.v`. I will reuse its `Z.quot` helper shape for midpoint bounds. For the two branch preservation witnesses, the proof should use sortedness: from `Znth mid l 0 >= target`, every later index is at least target; from `Znth mid l 0 < target`, every earlier index up to `mid` is below target. For the final `return -1` witness, `left >= right` and the invariant `left <= right` imply `left = right`; then indices below `left` use the prefix fact, and indices from `left` onward use either the failed equality at `left` or sortedness plus the suffix fact at `left`.

Planned edit to `coq/generated/binary_search_first_proof_manual.v`: add a local quotient-bounds helper, replace the six admitted bodies with conservative `pre_process` / `entailer!` scripts, use assertion-level `Right` for the `-1` postcondition disjunction, and keep all reasoning local to the generated manual file without adding axioms.

The edit succeeded. The final `proof_manual.v` contains:

```coq
Lemma binary_search_first_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.

Lemma proof_of_binary_search_first_entail_wit_3_1 : binary_search_first_entail_wit_3_1.
Proof.
  pre_process.
  assert (Hupper_new:
    forall j, mid <= j < n_pre -> target_pre <= Znth j l 0).
  ...
  sep_apply store_int_undef_store_int.
  entailer!.
Qed.

Lemma proof_of_binary_search_first_return_wit_2 : binary_search_first_return_wit_2.
Proof.
  pre_process.
  assert (Hleft_eq_right: left = right) by lia.
  assert (Hnot_found:
    forall j, 0 <= j < n_pre -> Znth j l 0 <> target_pre).
  ...
  Right.
  entailer!.
Qed.
```

The complete compile replay from `QualifiedCProgramming/SeparationLogic` succeeded for:

```text
binary_search_first_goal.v
binary_search_first_proof_auto.v
binary_search_first_proof_manual.v
binary_search_first_goal_check.v
```

`rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/binary_search_first_proof_manual.v` produced no matches. After compiling, non-`.v` Coq intermediates under the workspace `coq/` directory were deleted.
