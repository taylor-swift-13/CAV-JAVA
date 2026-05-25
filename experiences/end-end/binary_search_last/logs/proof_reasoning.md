## Manual proof iteration 1

Fresh `symexec` succeeded for `annotated/verify_20260422_093407_binary_search_last.c` and generated these current files:

```text
coq/generated/binary_search_last_goal.v
coq/generated/binary_search_last_proof_auto.v
coq/generated/binary_search_last_proof_manual.v
coq/generated/binary_search_last_goal_check.v
```

The generated manual proof file contains six admitted obligations:

```coq
Lemma proof_of_binary_search_last_safety_wit_2 : binary_search_last_safety_wit_2.
Lemma proof_of_binary_search_last_entail_wit_1 : binary_search_last_entail_wit_1.
Lemma proof_of_binary_search_last_entail_wit_2 : binary_search_last_entail_wit_2.
Lemma proof_of_binary_search_last_entail_wit_3_1 : binary_search_last_entail_wit_3_1.
Lemma proof_of_binary_search_last_entail_wit_3_2 : binary_search_last_entail_wit_3_2.
Lemma proof_of_binary_search_last_return_wit_2 : binary_search_last_return_wit_2.
```

The closest verified example is `examples/binary_search_first/coq/generated/binary_search_first_proof_manual.v`. Its proof structure applies directly after reversing the lower/upper-bound inequalities. The midpoint safety and midpoint assertion witnesses need the same quotient helper:

```coq
Lemma binary_search_last_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
```

`binary_search_last_entail_wit_3_1` is the branch where `Znth mid l 0 > target_pre` and the code executes `right = mid`; the proof must establish:

```coq
forall j, mid <= j < n_pre -> target_pre < Znth j l 0
```

For `j = mid`, this is the branch condition. For `mid < j`, monotonicity of the sorted list gives `Znth mid l 0 <= Znth j l 0`, and linear arithmetic closes the strict inequality.

`binary_search_last_entail_wit_3_2` is the branch where `Znth mid l 0 <= target_pre` and the code executes `left = mid + 1`; the proof must establish:

```coq
forall j, 0 <= j < mid + 1 -> Znth j l 0 <= target_pre
```

For old prefix indices `j < left`, use the invariant prefix fact. For `left <= j <= mid`, sortedness gives `Znth j l 0 <= Znth mid l 0`, then the branch condition closes the result.

The remaining nontrivial manual witness is `binary_search_last_return_wit_2`, the final `return -1` path after `left > 0` and `Znth (left - 1) l 0 <> target_pre`. At loop exit the generated hypotheses include `left >= right` and invariant `left <= right`, so `left = right`. To prove the not-found postcondition:

```coq
forall j, 0 <= j < n_pre -> Znth j l 0 <> target_pre
```

split on `j < left`. If `j < left`, sortedness plus `j <= left - 1`, the prefix upper bound at `left - 1`, and the explicit disequality at `left - 1` imply every prefix element is strictly below `target_pre`. If `left <= j`, then `right = left`, so the suffix invariant gives `target_pre < Znth j l 0`. The assertion-level disjunction must choose `Right`, matching the `__return == -1` postcondition branch.

## Manual proof iteration 2

The first `coqc` replay reached `binary_search_last_proof_manual.v` and failed before any mathematical subgoal because one `match goal` branch in `proof_of_binary_search_last_return_wit_2` omitted the required `|- _` separator:

```text
File ".../binary_search_last_proof_manual.v", line 141, characters 76-78:
Error: Syntax error: ',' or '|-' expected (in [match_context_rule]).
```

Failing tactic fragment:

```coq
match goal with
| Hupper: forall q, left <= q /\ q < n_pre -> target_pre < Znth q l 0 =>
    specialize (Hupper j ltac:(lia))
end.
```

This is a tactic syntax error, not a proof-state issue. I changed it to:

```coq
match goal with
| Hupper: forall q, left <= q /\ q < n_pre -> target_pre < Znth q l 0 |- _ =>
    specialize (Hupper j ltac:(lia))
end.
```

The next step is to rerun the full compile replay and inspect any real proof subgoal failures.
