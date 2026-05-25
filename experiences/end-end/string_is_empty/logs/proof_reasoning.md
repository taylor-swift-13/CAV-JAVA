# Proof Reasoning

## 2026-04-23 - Return witnesses after fresh symexec

Fresh `symexec` on `annotated/verify_20260423_030819_string_is_empty.c` succeeded and generated two manual obligations in `coq/generated/string_is_empty_proof_manual.v`:

```coq
Lemma proof_of_string_is_empty_return_wit_1 : string_is_empty_return_wit_1.
Proof. Admitted.

Lemma proof_of_string_is_empty_return_wit_2 : string_is_empty_return_wit_2.
Proof. Admitted.
```

The relevant generated goals are the two branch return witnesses. In the `s[0] == 0` branch, the precondition contains:

```coq
H  : Znth 0 (l ++ 0 :: nil) 0 = 0
H2 : Zlength l = n
H3 : forall k, 0 <= k < n -> Znth k l 0 <> 0
```

The postcondition branch to prove is the assertion-level right disjunct, which needs `n = 0` and `1 = 1`. If `n <> 0`, then `0 < n`; `app_Znth1` rewrites `Znth 0 (l ++ 0 :: nil) 0` to `Znth 0 l 0`, contradicting `H3 0`. Therefore `n = 0`, and the proof should use assertion-level `Right` followed by `entailer!`.

In the `s[0] != 0` branch, the precondition contains:

```coq
H  : Znth 0 (l ++ 0 :: nil) 0 <> 0
H2 : Zlength l = n
```

The postcondition branch to prove is the assertion-level left disjunct, which needs `0 < n` and `0 = 0`. If `n = 0`, the length equality gives `Zlength l = 0`; `app_Znth2` rewrites the read into the terminator cell, and after rewriting the zero length the hypothesis becomes `Znth 0 (0 :: nil) 0 <> 0`, a contradiction. Therefore `0 < n`, and the proof should use assertion-level `Left` followed by `entailer!`.

The generated proof file imports `List_lemma` but not `ListLib`; the manual proof needs `app_Znth1` and `app_Znth2`, so the planned edit adds `ListLib` to the existing AUXLib import line. No axioms or admitted lemmas are needed.
