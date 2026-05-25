# Proof reasoning

## 2026-04-22 manual obligations after fresh symexec

Fresh `symexec` generated `coq/generated/array_max_goal.v`, `array_max_proof_auto.v`, `array_max_proof_manual.v`, and `array_max_goal_check.v` for the active annotated file `annotated/verify_20260422_055419_array_max.c`.

The manual proof file contains two generated placeholders:

```coq
Lemma proof_of_array_max_entail_wit_1 : array_max_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_max_entail_wit_2_1 : array_max_entail_wit_2_1.
Proof. Admitted.
```

The relevant generated goals are:

```coq
Definition array_max_entail_wit_1 := 
forall (a_pre n_pre: Z) (l: list Z),
  1 <= n_pre /\ Zlength l = n_pre /\ IntArray.full a_pre n_pre l
|-- EX j_2,
  1 <= 1 /\ 1 <= n_pre /\ 0 <= j_2 /\ j_2 < 1 /\
  Znth j_2 l 0 = Znth 0 l 0 /\
  (forall j, 0 <= j /\ j < 1 -> Znth j l 0 <= Znth 0 l 0) /\
  1 <= n_pre /\ Zlength l = n_pre /\ IntArray.full a_pre n_pre l.
```

This is the invariant initialization proof. The witness should be `j_2 = 0`. After `Exists 0` and `entailer!`, the only nontrivial pure fact is the universal over `[0,1)`: for any `j`, `0 <= j /\ j < 1` implies `j = 0`, so the desired inequality is reflexive.

The second manual goal is the preservation case for the branch where `a[i] > ret` and the program executes `ret = a[i]`:

```coq
Definition array_max_entail_wit_2_1 :=
forall a_pre n_pre l ret j_3 i,
  Znth i l 0 > ret /\ i < n_pre /\ 1 <= i /\ i <= n_pre /\
  0 <= j_3 /\ j_3 < i /\ Znth j_3 l 0 = ret /\
  (forall j, 0 <= j /\ j < i -> Znth j l 0 <= ret) /\
  1 <= n_pre /\ Zlength l = n_pre /\ IntArray.full a_pre n_pre l
|-- EX j_2,
  1 <= i + 1 /\ i + 1 <= n_pre /\ 0 <= j_2 /\ j_2 < i + 1 /\
  Znth j_2 l 0 = Znth i l 0 /\
  (forall j, 0 <= j /\ j < i + 1 -> Znth j l 0 <= Znth i l 0) /\
  1 <= n_pre /\ Zlength l = n_pre /\ IntArray.full a_pre n_pre l.
```

Here the correct existential witness is the newly inspected index `j_2 = i`. After `Exists i` and `entailer!`, the only semantic proof is the universal for `[0, i + 1)`. For an arbitrary `j`, split on `j = i`. If equal, the inequality is reflexive. If `j <> i`, the range `0 <= j < i + 1` implies `j < i`; the old invariant gives `Znth j l 0 <= ret`, and the branch condition gives `ret < Znth i l 0`, so `lia` closes the transitive bound.

Planned replacement:

```coq
unfold <witness>.
intros.
Exists <chosen-index>.
entailer!.
intros j Hj.
...
```

This proof does not need helper lemmas because the remaining obligations are pure arithmetic and direct use of the existing quantified invariant.

## 2026-04-22 compile correction for quantified invariant hypothesis

First compile command:

```bash
coqc ... coq/generated/array_max_proof_manual.v
```

failed at `array_max_proof_manual.v`, line 43:

```text
Error: Illegal application (Non-functional construction): 
The expression "H5" of type "Znth j_3 l 0 = ret"
cannot be applied to the term "j" : "Z"
```

The proof body after `entailer!` had:

```coq
assert (0 <= j /\ j < i) by lia.
specialize (H5 j H0).
lia.
```

The generated goal orders the pure hypotheses as branch condition, bounds, witness facts, then the old universal invariant. In this context `H5` is the witness equality `Znth j_3 l 0 = ret`; the quantified invariant is `H6`:

```coq
H6 : forall j : Z, 0 <= j /\ j < i -> Znth j l 0 <= ret
```

The next edit is only to replace `H5` with `H6` in that `specialize`, keeping the same proof structure. This should leave the branch `j <> i` with the facts `Znth j l 0 <= ret` and `ret < Znth i l 0`, which `lia` can combine.

Second compile attempt reached the same line but failed because the freshly asserted range was named `H9`, while the script still passed `H0`:

```text
H0 : i < n_pre
H9 : 0 <= j < i
The term "H0" has type "i < n_pre" while it is expected to have type "0 <= j < i".
```

The local assertion is:

```coq
assert (0 <= j /\ j < i) by lia.
```

In this proof environment Coq prints the chained range as `0 <= j < i` and names it `H9`. The next edit specializes `H6` with `H9`, avoiding the unrelated loop-bound hypothesis.
