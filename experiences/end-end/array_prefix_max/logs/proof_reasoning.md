## Initial manual proof pass

After the successful `symexec` run, `coq/generated/array_prefix_max_proof_manual.v` contains nine admitted obligations:

```text
proof_of_array_prefix_max_safety_wit_5
proof_of_array_prefix_max_entail_wit_1
proof_of_array_prefix_max_entail_wit_2_1
proof_of_array_prefix_max_entail_wit_2_2
proof_of_array_prefix_max_entail_wit_3
proof_of_array_prefix_max_return_wit_1
proof_of_array_prefix_max_return_wit_2
proof_of_array_prefix_max_partial_solve_wit_6_pure
proof_of_array_prefix_max_which_implies_wit_1
```

The generated goals show three proof shapes:

1. Simple safety/entailment goals where `pre_process; entailer!; lia` should discharge arithmetic and heap cancellation.
2. Return witnesses: for `n == 0`, choose `lr = lo`; for loop exit, use `i_2 >= n_pre` and `i_2 <= n_pre` to derive `i_2 = n_pre`, then choose `lr = lr_2`.
3. Output write reconstruction: after `out[i] = cur`, choose `lr' = replace_Znth i cur lr`. This needs standard helper lemmas for `Zlength (replace_Znth ...)`, `Znth` at the replaced index, and `Znth` at other indices.

I will add local helper lemmas copied in shape from existing array-update proofs:

```coq
Zlength_replace_Znth
Znth_replace_Znth_same
Znth_replace_Znth_diff
```

The first compile attempt will use these helpers plus conservative scripts. If `coqc` exposes a specific remaining proof state, the next iteration will record the exact theorem, hypotheses, and subgoal before editing further.

## Compile failure: safety witness needs stack-slot int range

The first compile replay failed in:

```text
proof_of_array_prefix_max_safety_wit_5
Error: Attempt to save an incomplete proof
```

This theorem is the safety check for the loop increment after the output write. Its target in `array_prefix_max_goal.v` is:

```coq
[| (i + 1 <= INT_MAX) |] && [| (INT_MIN <= i + 1) |]
```

The left side contains the stack slot:

```coq
(&( "i" )) # Int |-> i
```

but the first script only ran `pre_process; entailer!`, so Coq did not recover the integer range for `i`. Following the compile/proof experience for overflow witnesses, I will apply:

```coq
prop_apply (store_int_range (&("i")) i).
Intros.
```

before `entailer!`; together with the invariant facts `1 <= i` and `i < n_pre`, this should expose `Int.min_signed <= i <= Int.max_signed` and allow the increment range proof to close by arithmetic.

## Final proof pass

After removing intra-loop `Assert` annotations that caused local scalar stores to disappear, symbolic execution generated only five manual obligations:

```text
proof_of_array_prefix_max_entail_wit_1
proof_of_array_prefix_max_entail_wit_2_1
proof_of_array_prefix_max_entail_wit_2_2
proof_of_array_prefix_max_return_wit_1
proof_of_array_prefix_max_return_wit_2
```

The final manual proof uses local list-update helper lemmas for `replace_Znth` and proves the two loop-preservation branches by choosing the updated output list:

```coq
replace_Znth i cur lr_2
replace_Znth i (Znth i la 0) lr_2
```

Important proof details:

- The generated prefix-maximum invariant parses as `exists j, (range /\ equality) /\ max_property`, so witness proofs must split the existential body as a pair whose first component is itself a pair.
- In the `a[i] <= cur` branch, the new output at index `i` reuses the old witness for index `i - 1`; the max property comes from the old prefix invariant.
- In the `a[i] > cur` branch, the witness for the new index is `i`; old prefix bounds plus the branch comparison prove the new maximum property.
- Return witness proofs are closed directly by `entailer!` after choosing `lr_2` for nonempty exit and `lo` for the empty case.

Final compile status:

```text
array_prefix_max_goal.v: passed
array_prefix_max_proof_auto.v: passed
array_prefix_max_proof_manual.v: passed
array_prefix_max_goal_check.v: passed
```

`array_prefix_max_proof_manual.v` contains no local `Admitted`, `admit`, or `Axiom` declarations. The generated auto proof file still contains generated admits, so the fingerprint records `auto_proof_contains_admitted`.
