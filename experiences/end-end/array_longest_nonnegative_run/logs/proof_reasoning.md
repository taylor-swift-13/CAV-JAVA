# Proof Reasoning

## 2026-04-22 05:49 manual witness plan

After `symexec`, `coq/generated/array_longest_nonnegative_run_proof_manual.v`
contains five admitted manual witnesses:

```coq
Lemma proof_of_array_longest_nonnegative_run_entail_wit_1 : array_longest_nonnegative_run_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_longest_nonnegative_run_entail_wit_2_1 : array_longest_nonnegative_run_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_longest_nonnegative_run_entail_wit_2_2 : array_longest_nonnegative_run_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_longest_nonnegative_run_entail_wit_2_3 : array_longest_nonnegative_run_entail_wit_2_3.
Proof. Admitted.

Lemma proof_of_array_longest_nonnegative_run_return_wit_1 : array_longest_nonnegative_run_return_wit_1.
Proof. Admitted.
```

The core hypothesis in the loop-preservation witnesses has this shape:

```coq
array_longest_nonnegative_run_acc current best (sublist i n_pre l) =
array_longest_nonnegative_run_spec l
```

For each branch, the goal needs the same equality after consuming `l[i]` and
moving to `sublist (i + 1) n_pre l`. The missing bridge is a pure list lemma:

```coq
sublist i n l = Znth i l 0 :: sublist (i + 1) n l
```

under `0 <= i < n` and `n <= Zlength l`. Once this rewrite is applied to the
accumulator hypothesis, simplification unfolds the first recursive step of
`array_longest_nonnegative_run_acc`. The positive branch then splits on
`Z_le_dec 0 (Znth i l 0)` and uses the branch guard `Znth i l 0 >= 0`. The
`current + 1 > best` sub-branch rewrites `Z.max best (current + 1)` to
`current + 1`; the `current + 1 <= best` sub-branch rewrites it to `best`.
The negative branch uses the guard `Znth i l 0 < 0`, so the accumulator resets
to `array_longest_nonnegative_run_acc 0 best (sublist (i + 1) n_pre l)`.

The return witness has hypotheses:

```coq
i >= n_pre
i <= n_pre
array_longest_nonnegative_run_acc current best (sublist i n_pre l) =
array_longest_nonnegative_run_spec l
```

First prove `i = n_pre` by `lia`, then rewrite `sublist n_pre n_pre l` to
`nil`. The accumulator over `nil` simplifies to `best`, giving the required
`best = array_longest_nonnegative_run_spec l`.

The proof edit will add the helper lemma directly to this task's
`proof_manual.v` and replace all five `Admitted.` bodies. It does not add any
axiom and does not modify generated goals.
