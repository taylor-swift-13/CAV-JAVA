## 2026-04-23 12:11 manual witnesses after successful symexec

Fresh symbolic execution succeeded on `annotated/verify_20260423_120929_string_last_char.c` and generated:

```text
string_last_char_goal.v
string_last_char_proof_auto.v
string_last_char_proof_manual.v
string_last_char_goal_check.v
```

The manual proof file contains exactly three admitted obligations:

```coq
Lemma proof_of_string_last_char_entail_wit_2 : string_last_char_entail_wit_2.
Proof. Admitted.

Lemma proof_of_string_last_char_entail_wit_3 : string_last_char_entail_wit_3.
Proof. Admitted.

Lemma proof_of_string_last_char_return_wit_1 : string_last_char_return_wit_1.
Proof. Admitted.
```

The relevant generated goals are pure/list bridge facts over the unchanged heap:

```coq
string_last_char_entail_wit_2:
  Znth (i + 1) (l ++ 0 :: nil) 0 <> 0,
  0 <= i, i < n, Zlength l = n,
  forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0
  |-- i + 1 < n

string_last_char_entail_wit_3:
  Znth (i + 1) (l ++ 0 :: nil) 0 = 0,
  0 <= i, i < n, Zlength l = n,
  forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0
  |-- i = n - 1

string_last_char_return_wit_1:
  i = n - 1, 1 <= n, Zlength l = n
  |-- Znth i (l ++ 0 :: nil) 0 = Znth (n - 1) l 0
```

These are semantically provable from the contract: the prefix `l` has length `n` and all payload elements are nonzero, so the only zero in `l ++ [0]` at an index between `0` and `n` is the terminator at `n`. I checked `examples/string_ends_with_char/coq/generated/string_ends_with_char_proof_manual.v`, which has byte-for-byte matching helper lemma shapes for this scan-to-last-character loop:

```coq
app_zero_nonzero_implies_lt
app_zero_eq_zero_implies_length
app_zero_last_value
```

Planned proof edit: add those local helper lemmas to the current manual proof and prove each witness with `unfold`, `pre_process`, one explicit helper assertion, and `entailer!`. No `Axiom` or `Admitted` will remain in `proof_manual.v`.

## 2026-04-23 12:12 return witness helper inference failure

The first strict compile replay compiled `string_last_char_goal.v` and `string_last_char_proof_auto.v`, then stopped in the manual return witness:

```text
File ".../string_last_char_proof_manual.v", line 106, characters 2-36:
Error: Unable to find an instance for the variable n.
```

The failing proof fragment was:

```coq
Lemma proof_of_string_last_char_return_wit_1 : string_last_char_return_wit_1.
Proof.
  unfold string_last_char_return_wit_1.
  pre_process.
  rewrite app_zero_last_value by lia.
  entailer!.
Qed.
```

The problem is not a missing semantic fact. After `pre_process`, the context includes `i = n - 1`, `1 <= n`, and `Zlength l = n`, which are exactly the premises of `app_zero_last_value`. The issue is Coq's rewrite inference: the lemma has parameters `(l n i)`, and the target contains both `Znth i (l ++ 0 :: nil) 0` and `Znth (n - 1) l 0`, so the unqualified rewrite did not infer `n` robustly.

Next edit: call the helper with explicit arguments in the return witness:

```coq
rewrite (app_zero_last_value l n i) by lia.
```

This keeps the proof local and leaves the two already compiled entailment witnesses unchanged.
