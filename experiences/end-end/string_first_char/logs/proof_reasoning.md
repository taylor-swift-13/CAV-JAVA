# Proof Reasoning

## Manual witness `proof_of_string_first_char_return_wit_1`

Fresh `symexec` succeeded for `annotated/verify_20260423_025022_string_first_char.c` and generated one manual obligation in `coq/generated/string_first_char_proof_manual.v`:

```coq
Lemma proof_of_string_first_char_return_wit_1 : string_first_char_return_wit_1.
Proof. Admitted.
```

The corresponding VC in `string_first_char_goal.v` is:

```coq
Definition string_first_char_return_wit_1 :=
forall (s_pre: Z) (n: Z) (l: list Z),
  [| 1 <= n |] &&
  [| n < INT_MAX |] &&
  [| Zlength l = n |] &&
  [| forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0 |] &&
  CharArray.full s_pre (n + 1) (app l (cons 0 nil))
|--
  [| Znth 0 (app l (cons 0 nil)) 0 = Znth 0 l 0 |] &&
  CharArray.full s_pre (n + 1) (app l (cons 0 nil)).
```

The spatial resource on the right is exactly the same `CharArray.full` resource as the left, so the separation-logic part should be handled by `pre_process; entailer!`. The only semantic bridge is the pure list fact that index `0` of `l ++ [0]` equals index `0` of `l`; this is valid because `Zlength l = n` and `1 <= n` imply `0 < Zlength l`. I will keep the proof local to `proof_manual.v`, with no new axiom and no change to any generated goal file.

## Compile feedback: local list lemma name

The first compile replay reached `string_first_char_proof_manual.v` and failed at line 25:

```text
Error: The variable Znth_app1 was not found in the current environment.
```

The proof shape was otherwise:

```coq
pre_process.
entailer!.
rewrite Znth_app1; lia.
```

Searching the imported local libraries showed the available lemma is named `app_Znth1`:

```coq
Lemma app_Znth1:
  0 <= i < Zlength l -> Znth i (l ++ l') d = Znth i l d.
```

The next patch keeps the same proof structure and changes only the lemma name to `app_Znth1`, with `lia` discharging `0 <= 0 < Zlength l` from `Zlength l = n` and `1 <= n`.
