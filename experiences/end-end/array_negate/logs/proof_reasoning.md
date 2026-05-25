# Proof Reasoning

## 2026-04-22 06:24:25 +0800 - Replace four generated manual placeholders

- After successful `symexec`, `coq/generated/array_negate_proof_manual.v` contains four manual obligations, all still admitted:

```coq
Lemma proof_of_array_negate_safety_wit_2 : array_negate_safety_wit_2.
Proof. Admitted.

Lemma proof_of_array_negate_entail_wit_1 : array_negate_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_negate_entail_wit_2 : array_negate_entail_wit_2.
Proof. Admitted.

Lemma proof_of_array_negate_return_wit_1 : array_negate_return_wit_1.
Proof. Admitted.
```

- Current generated goal shapes:
  - `array_negate_safety_wit_2` must prove `Znth i la 0 <> INT_MIN` from the contract guard `INT_MIN <= -Znth i la 0 <= INT_MAX` and the loop branch fact `0 <= i < n_pre`.
  - `array_negate_entail_wit_1` initializes the loop invariant. The intended witnesses are `l1 = nil` and `l2 = lo`, so `app l1 l2` is the original output list.
  - `array_negate_entail_wit_2` preserves the loop invariant after the write. The left heap is:

```coq
IntArray.full out_pre n_pre
  (replace_Znth i_2 (-(Znth i_2 la 0)) (app l1_2 l2_2))
```

The intended right-hand invariant witnesses are:

```coq
l1 = l1_2 ++ cons (-(Znth i_2 la 0)) nil
l2 = sublist (i_2 + 1) n_pre lo
```

To make the heap lists syntactically match, first prove `l2_2 = sublist i_2 n_pre lo` from the invariant's suffix fact, rewrite `replace_Znth` through the `app` boundary, split `sublist i_2 n_pre lo` into the current element plus tail, and show that replacing at the prefix boundary leaves `l1_2` unchanged.
  - `array_negate_return_wit_1` exits the loop. From `i_3 >= n_pre` and `i_3 <= n_pre`, prove `i_3 = n_pre`; then `Zlength l2 = 0`, so `l2 = nil`. Use `lr = l1` and the prefix semantic fact to prove every output element is `-la[i]`.

- Reusable proof pattern: this is the same prefix/suffix output-array proof shape as `array_scale`, with the pointwise expression changed from `la[i] * k` to `-la[i]`. The proof should stay local to `proof_manual.v` and should not require changing the annotation unless compilation shows the generated witness lacks a needed heap or parameter-stability fact.

## 2026-04-22 06:26:18 +0800 - First proof compile failed in safety witness pattern match

- Compile command reached `array_negate_proof_manual.v` after successfully compiling `array_negate_goal.v` and `array_negate_proof_auto.v`.
- Stable failure:

```text
File ".../coq/generated/array_negate_proof_manual.v", line 25, characters 2-185:
Error: No matching clauses for match.
```

- Failing proof fragment:

```coq
match goal with
| H : forall i : Z, 0 <= i /\ i < n_pre ->
      INT_MIN <= - Znth i la 0 /\ - Znth i la 0 <= INT_MAX |- _ =>
    pose proof (H i ltac:(lia)) as Hrange;
    lia
end.
```

- Diagnosis from `coqtop Show`: after `pre_process; entailer!`, the overflow guard is named `H11`, but `INT_MIN` and `INT_MAX` have already simplified to concrete bounds:

```coq
H11 :
  forall i_2 : Z,
  0 <= i_2 < n_pre -> -2147483648 <= - Znth i_2 la 0 <= 2147483647
============================
Znth i la 0 <> -2147483648
```

The match pattern was too syntactic because it expected `INT_MIN`/`INT_MAX` rather than the simplified numerals.

- Next edit: avoid the brittle match pattern and use the stable generated hypothesis name in this witness:

```coq
pose proof (H11 i ltac:(lia)) as Hrange.
lia.
```

## 2026-04-22 06:27:07 +0800 - Return witness needed range normalized to `Zlength l1`

- Compile command again reached `array_negate_proof_manual.v`; safety, initial invariant, and loop-preservation obligations passed far enough for the compiler to fail in `proof_of_array_negate_return_wit_1`.
- Stable failure:

```text
File ".../array_negate_proof_manual.v", line 140, characters 8-10:
The term "Hi" has type "0 <= i < n_pre" while it is expected to have type
"0 <= i < Zlength l1".
```

- Current proof state around the failure contains:

```coq
H6 : forall t : Z, 0 <= t < Zlength l1 -> Znth t l1 0 = - Znth t la 0
H12 : Zlength l1 = n_pre
i : Z
Hi : 0 <= i < n_pre
```

- Diagnosis: after proving loop exit and `l2 = nil`, `entailer!` rewrote the prefix semantic hypothesis to use `Zlength l1` rather than `n_pre`. This is not an annotation problem: `H12` explicitly gives `Zlength l1 = n_pre`.
- Next edit: when applying `H6`, rewrite `H12` in the required range side condition:

```coq
apply H6.
rewrite H12.
exact Hi.
```
