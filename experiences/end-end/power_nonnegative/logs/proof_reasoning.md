# Proof reasoning

## 2026-04-22 manual witnesses after first successful `symexec`

Fresh `symexec` generated:

```text
power_nonnegative_goal.v
power_nonnegative_proof_auto.v
power_nonnegative_proof_manual.v
power_nonnegative_goal_check.v
```

The generated manual file contains exactly three unfinished lemmas:

```coq
Lemma proof_of_power_nonnegative_safety_wit_3 : power_nonnegative_safety_wit_3.
Proof. Admitted.

Lemma proof_of_power_nonnegative_entail_wit_1 : power_nonnegative_entail_wit_1.
Proof. Admitted.

Lemma proof_of_power_nonnegative_entail_wit_3 : power_nonnegative_entail_wit_3.
Proof. Admitted.
```

`power_nonnegative_entail_wit_1` is loop invariant initialization. Its only nontrivial pure fact is `1 = power_nonnegative_z base_pre 0`, which follows by unfolding `power_nonnegative_z`; a direct `pre_process` run already solved this witness in `coqtop`.

`power_nonnegative_safety_wit_3` is the multiplication overflow witness. After:

```coq
pre_process.
```

the remaining state was:

```coq
H  : 0 <= i
H0 : i < exp_pre
H9 : forall k_3 : Z,
       0 <= k_3 <= exp_pre ->
       -2147483648 <= power_nonnegative_z base_pre k_3 <= 2147483647
---
&( "i") # Int |-> i ** ... ** &( "ans") # Int |-> power_nonnegative_z base_pre i
|-- [|power_nonnegative_z base_pre i * base_pre <= 2147483647|] &&
    [|-2147483648 <= power_nonnegative_z base_pre i * base_pre|]
```

This is semantically provable from the contract range fact instantiated at `k = i + 1`, but the goal first needs the recurrence:

```coq
power_nonnegative_z base (i + 1) = power_nonnegative_z base i * base
```

I am adding a local helper lemma `power_nonnegative_z_succ` proved by unfolding `power_nonnegative_z`, rewriting `Z.to_nat (i + 1)` as `Z.to_nat i + Z.to_nat 1` under `0 <= i`, and simplifying the recursive definition. Then `safety_wit_3` rewrites the multiplication into `power_nonnegative_z base_pre (i + 1)`, uses `entailer!` to split the two pure bounds, and instantiates the range hypothesis with `0 <= i + 1 <= exp_pre`.

`power_nonnegative_entail_wit_3` is the post-assignment assertion bridge. After `pre_process`, its heap cell is:

```coq
&( "ans") # Int |-> (power_nonnegative_z base_pre i * base_pre)
```

while the target assertion expects:

```coq
&( "ans") # Int |-> power_nonnegative_z base_pre (i + 1)
```

The same `power_nonnegative_z_succ` rewrite changes the source heap cell to the target value; `entailer!` then solves the remaining duplicated pure facts and heap frame.
