# Proof Reasoning

## 2026-04-22 18:50 manual witnesses for `longest_increasing_run`

After the successful `symexec` pass, the generated manual file contains six
admitted witnesses:

```coq
Lemma proof_of_longest_increasing_run_entail_wit_1 : longest_increasing_run_entail_wit_1.
Proof. Admitted.

Lemma proof_of_longest_increasing_run_entail_wit_2_1 : longest_increasing_run_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_longest_increasing_run_entail_wit_2_2 : longest_increasing_run_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_longest_increasing_run_entail_wit_2_3 : longest_increasing_run_entail_wit_2_3.
Proof. Admitted.

Lemma proof_of_longest_increasing_run_return_wit_1 : longest_increasing_run_return_wit_1.
Proof. Admitted.

Lemma proof_of_longest_increasing_run_return_wit_2 : longest_increasing_run_return_wit_2.
Proof. Admitted.
```

The corresponding goals in `longest_increasing_run_goal.v` are all pure
entailments over `IntArray.full` plus arithmetic/list facts. The core invariant
fact is:

```coq
longest_increasing_run_acc
  (Znth (i - 1) l 0) cur best (sublist i n_pre l) =
longest_increasing_run_spec l
```

For the three preservation witnesses, the proof needs to rewrite the nonempty
suffix at loop index `i`:

```coq
sublist i n_pre l = Znth i l 0 :: sublist (i + 1) n_pre l
```

Then the Coq accumulator unfolds exactly according to the C branch:

```coq
if Z_lt_dec (Znth (i - 1) l 0) (Znth i l 0) then
  longest_increasing_run_acc (Znth i l 0) (cur + 1)
    (Z.max best (cur + 1)) (sublist (i + 1) n_pre l)
else
  longest_increasing_run_acc (Znth i l 0) 1 best
    (sublist (i + 1) n_pre l)
```

This means the manual proof should add three local helpers:

```coq
Lemma sublist_head_cons_Z : ...
Lemma longest_increasing_run_spec_nonempty_acc : ...
Lemma longest_increasing_run_acc_step : ...
```

`entail_wit_1` uses the nonempty initialization helper to establish the loop
invariant at `i = 1`, `cur = 1`, `best = 1`. `entail_wit_2_1` is the increasing
branch where `best < cur + 1`, so `Z.max best (cur + 1) = cur + 1`.
`entail_wit_2_2` is the non-increasing branch where the current run resets to
`1` and `best` is preserved. `entail_wit_2_3` is the increasing branch where
`best >= cur + 1`, so `Z.max best (cur + 1) = best`. The zero return witness
uses `Zlength_nil_inv`; the loop-exit return witness derives `i = n_pre`,
rewrites the suffix to `nil`, and reduces the accumulator to `best`.

These are proof-only changes in
`coq/generated/longest_increasing_run_proof_manual.v`; the latest generated
witnesses contain the needed array ownership, bounds, and accumulator invariant.
