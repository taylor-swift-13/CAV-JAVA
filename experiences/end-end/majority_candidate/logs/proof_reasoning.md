# Proof reasoning

## Manual witnesses after successful `symexec`

Latest `symexec` completed and generated `coq/generated/majority_candidate_goal.v`, `majority_candidate_proof_auto.v`, `majority_candidate_proof_manual.v`, and `majority_candidate_goal_check.v`.

The manual file contains five admitted entailment lemmas:

```coq
Lemma proof_of_majority_candidate_entail_wit_1 : majority_candidate_entail_wit_1.
Lemma proof_of_majority_candidate_entail_wit_2_1 : majority_candidate_entail_wit_2_1.
Lemma proof_of_majority_candidate_entail_wit_2_2 : majority_candidate_entail_wit_2_2.
Lemma proof_of_majority_candidate_entail_wit_2_3 : majority_candidate_entail_wit_2_3.
Lemma proof_of_majority_candidate_entail_wit_3 : majority_candidate_entail_wit_3.
```

The goals are pure/list obligations around the loop invariant.  The spatial part is always unchanged `IntArray.full a_pre n_pre l`, so `pre_process` and `entailer!` should handle the separation part after the needed pure facts are prepared.

The initialization witness needs:

```coq
majority_candidate_acc (Znth 0 l 0) 1 (sublist 1 n_pre l) =
majority_candidate_spec l
```

under `1 <= n_pre` and `Zlength l = n_pre`.  This follows by destructing the nonempty list and normalizing `sublist 1 (Zlength (x :: xs)) (x :: xs)` to `xs`.

The three preservation witnesses all need the same suffix-head decomposition:

```coq
sublist i n l = Znth i l 0 :: sublist (i + 1) n l
```

when `0 <= i < n` and `n <= Zlength l`.  After rewriting this into the invariant hypothesis

```coq
majority_candidate_acc candidate count (sublist i n_pre l) =
majority_candidate_spec l
```

the definition of `majority_candidate_acc` exposes exactly the C branch:

```coq
if Z.eq_dec count 0 then ...
else if Z.eq_dec (Znth i l 0) candidate then ...
else ...
```

The exit witness `majority_candidate_entail_wit_3` needs `i = n_pre` from `i >= n_pre` and `i <= n_pre`, then `sublist n_pre n_pre l = nil`, so `majority_candidate_acc candidate count nil` reduces to `candidate` and yields `candidate = majority_candidate_spec l`.

Planned edit in `coq/generated/majority_candidate_proof_manual.v`:

1. Add local helper lemmas `majority_candidate_sublist_head`, `majority_candidate_spec_nonempty`, and `majority_candidate_acc_sublist_step`.
2. Replace all five `Admitted.` bodies with proofs that first derive the relevant accumulator equality, then call `entailer!`.
3. Compile all generated files and inspect the exact proof state if the first script does not compile.

## First proof compile failure: hypothesis numbering

The first full compile reached `proof_of_majority_candidate_entail_wit_2_1` and failed with:

```text
File ".../majority_candidate_proof_manual.v", line 104, characters 4-29:
Error: Found no subterm matching
"majority_candidate_acc candidate count (sublist i n_pre l)" in H6.
```

Using `coqtop` with the same imports as the generated proof showed that after `pre_process` the invariant equality in this witness is `H5`, not `H6`:

```coq
H5 :
  majority_candidate_acc candidate count (sublist i n_pre l) =
  majority_candidate_spec l
H6 : 1 <= n_pre
H7 : n_pre <= 2147483647
H8 : Zlength l = n_pre
```

For `entail_wit_2_2` and `entail_wit_2_3`, the equality is `H6`.  For `entail_wit_3`, the equality is `H4`:

```coq
H4 :
  majority_candidate_acc candidate count (sublist i n_pre l) =
  majority_candidate_spec l
```

I will only adjust those hypothesis references; the proof structure and helper lemmas remain unchanged.

## Second proof compile failure: same issue in `entail_wit_2_2`

The next compile reached `proof_of_majority_candidate_entail_wit_2_2` and failed with:

```text
File ".../majority_candidate_proof_manual.v", line 123, characters 4-29:
Error: Found no subterm matching
"majority_candidate_acc candidate count (sublist i n_pre l)" in H7.
```

The earlier `coqtop` state for this witness showed:

```coq
H6 :
  majority_candidate_acc candidate count (sublist i n_pre l) =
  majority_candidate_spec l
H7 : 1 <= n_pre
```

So the rewrite and final `exact` in `entail_wit_2_2` must use `H6`, not `H7`.

## Third proof compile failure: same issue in `entail_wit_2_3`

The next compile reached `proof_of_majority_candidate_entail_wit_2_3` and failed with the same shape:

```text
File ".../majority_candidate_proof_manual.v", line 144, characters 4-29:
Error: Found no subterm matching
"majority_candidate_acc candidate count (sublist i n_pre l)" in H7.
```

The `coqtop` state for `entail_wit_2_3` also has the accumulator equality at `H6`; `H7` is the lower-bound fact `1 <= n_pre`.  I will switch that rewrite and `exact` to `H6`.
