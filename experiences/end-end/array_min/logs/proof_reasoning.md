# Proof reasoning

## 2026-04-22 manual entailment witnesses

After successful `symexec`, `coq/generated/array_min_proof_manual.v` contains two admitted manual lemmas:

```coq
Lemma proof_of_array_min_entail_wit_1 : array_min_entail_wit_1.
Proof. Admitted.

Lemma proof_of_array_min_entail_wit_2_1 : array_min_entail_wit_2_1.
Proof. Admitted.
```

`array_min_entail_wit_1` is the invariant initialization obligation. The goal asks for an existential `idx` such that `0 <= idx < 1`, `Znth idx l 0 = Znth 0 l 0`, and every `j` in `[0, 1)` satisfies `Znth 0 l 0 <= Znth j l 0`. Choosing `idx = 0` leaves only the arithmetic fact that any integer `j` with `0 <= j < 1` is `0`.

`array_min_entail_wit_2_1` is the loop-preservation obligation for the branch:

```coq
[| Znth i l 0 < ret |] &&
[| forall j, 0 <= j /\ j < i -> ret <= Znth j l 0 |]
|--
EX idx,
  [| Znth idx l 0 = Znth i l 0 |] &&
  [| forall j, 0 <= j /\ j < i + 1 -> Znth i l 0 <= Znth j l 0 |] && ...
```

This branch assigns `ret = a[i]`, so the correct existential witness is `idx = i`. For the new universal prefix-min fact, split any `j < i + 1` into `j = i` or `j < i`. The `j = i` case is reflexive arithmetic. The `j < i` case uses the old invariant `ret <= Znth j l 0` and the branch fact `Znth i l 0 < ret`, so `Znth i l 0 <= Znth j l 0` follows by `lia`.

The proof script mirrors the already verified `array_max` entailment pattern, with inequality directions reversed. It uses assertion-level `Exists`, `entailer!`, a small index case split, and `lia`; no helper lemma is needed.

## 2026-04-22 compile failure in generic hypothesis match

First compile attempt failed in `array_min_proof_manual.v`:

```text
File ".../array_min_proof_manual.v", line 43, characters 4-138:
Error: No matching clauses for match.
```

The failing fragment was:

```coq
match goal with
| Hforall : forall x : Z, (0 <= x /\ x < i) -> ret <= Znth x l 0 |- _ =>
    specialize (Hforall j H)
end.
```

The proof state after `unfold`, `intros`, `Exists i`, and `entailer!` still contains the old invariant universal fact, but the exact parsed form does not match that tactic pattern. I first guessed the old prefix-min fact as `H7`; the next compile showed this was wrong:

```text
The expression "H7" of type "Znth idx_2 l 0 = ret"
cannot be applied to the term "j" : "Z"
```

So `H7` is the occurrence equality and the old prefix-min universal is the next hypothesis, `H8`. I will keep the named local range assertion `Hj_old` and specialize `H8 j Hj_old`.
