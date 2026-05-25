## Proof iteration 1

After symexec, the generated manual file contains five admitted obligations:

```coq
Lemma proof_of_array_sum_even_indices_safety_wit_6 : array_sum_even_indices_safety_wit_6.
Proof. Admitted.

Lemma proof_of_array_sum_even_indices_entail_wit_1 : array_sum_even_indices_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_sum_even_indices_entail_wit_2_1 : array_sum_even_indices_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_sum_even_indices_entail_wit_2_2 : array_sum_even_indices_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_sum_even_indices_entail_wit_3 : array_sum_even_indices_entail_wit_3.
Proof. Admitted.
```

The key generated goals are pure list/arithmetic obligations over the invariant:

```coq
sum = array_sum_even_indices_spec (sublist 0 i l)
```

For the even branch, `safety_wit_6` must prove:

```coq
INT_MIN <= sum + Znth i l 0 /\ sum + Znth i l 0 <= INT_MAX
```

The input contract already provides prefix bounds for every `k`:

```coq
forall k,
  0 <= k /\ k <= n_pre ->
  INT_MIN <= array_sum_even_indices_spec (sublist 0 k l) /\
  array_sum_even_indices_spec (sublist 0 k l) <= INT_MAX
```

so the proof should instantiate it with `k = i + 1`, then rewrite
`array_sum_even_indices_spec (sublist 0 (i + 1) l)` to
`array_sum_even_indices_spec (sublist 0 i l) + Znth i l 0` under the even-index hypothesis.

The two loop-preservation entailments need the same prefix-extension facts:

```coq
array_sum_even_indices_spec (sublist 0 (i + 1) l) =
array_sum_even_indices_spec (sublist 0 i l) + Znth i l 0
```

when `i` is even, and

```coq
array_sum_even_indices_spec (sublist 0 (i + 1) l) =
array_sum_even_indices_spec (sublist 0 i l)
```

when `i` is odd. These are not separation-logic problems; they are list facts about a recursive spec that skips every second element. I found the archived verified workspace `verify_20260420_114610_array_sum_even_indices`, whose generated goal shape and C invariant match this current workspace. Its manual proof uses four local helper lemmas:

```coq
array_sum_even_indices_spec_app_single_even
array_sum_even_indices_spec_app_single_odd
array_sum_even_indices_spec_sublist_snoc_even
array_sum_even_indices_spec_sublist_snoc_odd
```

These helpers are reusable for this exact current witness shape. I will copy their proof structure into the current `array_sum_even_indices_proof_manual.v`, keeping the current generated import path:

```coq
From SimpleC.EE Require Import array_sum_even_indices_goal.
```

and replacing the five admitted proofs with completed proofs. No `Axiom` will be added. The simple initialization witness should close with `entailer!`; the exit witness should prove `i = n_pre`, rewrite `Zlength l = n_pre`, and use `sublist_self`.
