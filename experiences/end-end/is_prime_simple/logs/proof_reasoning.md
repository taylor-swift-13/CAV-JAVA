## 2026-04-22 return witness proof plan

After the final `symexec` pass, `coq/generated/is_prime_simple_proof_manual.v` contains exactly three manual placeholders:

```coq
Lemma proof_of_is_prime_simple_return_wit_1 : is_prime_simple_return_wit_1.
Proof. Admitted.

Lemma proof_of_is_prime_simple_return_wit_2 : is_prime_simple_return_wit_2.
Proof. Admitted.

Lemma proof_of_is_prime_simple_return_wit_3 : is_prime_simple_return_wit_3.
Proof. Admitted.
```

The relevant generated goals are pure return-spec obligations:

```coq
is_prime_simple_return_wit_1:
  n_pre < 2 -> 0 <= n_pre -> is_prime_simple_spec n_pre 0

is_prime_simple_return_wit_2:
  n_pre % d = 0 -> d < n_pre -> 2 <= d -> ... -> is_prime_simple_spec n_pre 0

is_prime_simple_return_wit_3:
  2 <= n_pre ->
  (forall k, 2 <= k < n_pre -> n_pre % k <> 0) ->
  is_prime_simple_spec n_pre 1
```

The Coq specification from `original/is_prime_simple.v` is:

```coq
Definition is_prime_z (n : Z) : Prop :=
  1 < n /\ forall d, 2 <= d < n -> Z.rem n d <> 0.

Definition is_prime_simple_spec (n r : Z) : Prop :=
  (r = 1 /\ is_prime_z n) \/
  (r = 0 /\ ~ is_prime_z n).
```

Proof approach:

- `return_wit_1`: choose the right disjunct (`r = 0 /\ ~ is_prime_z n`). If `is_prime_z n` held, its first conjunct `1 < n` would contradict `n < 2`.
- `return_wit_2`: choose the right disjunct. If `is_prime_z n` held, specialize its universal divisor condition at the current `d`; the path facts `2 <= d` and `d < n` make the range valid, contradicting `n % d = 0`.
- `return_wit_3`: choose the left disjunct (`r = 1 /\ is_prime_z n`). The lower bound `2 <= n` proves `1 < n`, and the loop-exit assertion already provides the universal nonzero-remainder condition.

I will keep each witness proof local and avoid adding any axiom or global helper, because these are direct arithmetic/spec splits after `pre_process; entailer!`.

## 2026-04-22 first proof compile fix

The first full compile stopped in `is_prime_simple_proof_manual.v` at the second witness:

```text
line 29, characters 22-24:
Error: Syntax error: ']' expected after [for_each_goal] (in [ltac_expr]).
```

The failing line used an inline tactic argument:

```coq
contradiction (Hprime ltac:(lia)).
```

This syntax is brittle in this proof context. I will replace it with a named range assertion:

```coq
assert (Hd_range : 2 <= d < n_pre) by lia.
specialize (Hprime d Hd_range).
contradiction.
```

This keeps the proof obligation explicit and avoids relying on Ltac-in-term parsing inside `contradiction`.

The next compile still pointed at line 29, now identified as:

```coq
split; [reflexivity |].
```

Under the generated file's local scopes, the empty second branch notation is parsed poorly. I will rewrite all three witnesses to use explicit bullets:

```coq
split.
- reflexivity.
- ...
```

This avoids the fragile bracket form and makes the two conjunct proofs independent.
