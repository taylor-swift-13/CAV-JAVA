# Proof reasoning

## 2026-04-22 manual witnesses after successful symexec

Fresh `symexec` succeeded for `annotated/verify_20260422_034412_array_count_zero.c` and generated:

```text
coq/generated/array_count_zero_goal.v
coq/generated/array_count_zero_proof_auto.v
coq/generated/array_count_zero_proof_manual.v
coq/generated/array_count_zero_goal_check.v
```

The generated manual file currently contains five admitted obligations:

```coq
proof_of_array_count_zero_safety_wit_4
proof_of_array_count_zero_entail_wit_1
proof_of_array_count_zero_entail_wit_2_1
proof_of_array_count_zero_entail_wit_2_2
proof_of_array_count_zero_entail_wit_3
```

The corresponding goal shapes are:

```coq
array_count_zero_safety_wit_4:
  Znth i l 0 = 0 ->
  i < n_pre -> 0 <= i -> i <= n_pre ->
  count = array_count_zero_spec (sublist 0 i l) ->
  0 <= n_pre -> Zlength l = n_pre ->
  ... |-- count + 1 <= INT_MAX /\ INT_MIN <= count + 1

array_count_zero_entail_wit_2_1:
  Znth i l 0 = 0 ->
  count = array_count_zero_spec (sublist 0 i l) ->
  ... |-- count + 1 =
          array_count_zero_spec (sublist 0 (i + 1) l)

array_count_zero_entail_wit_2_2:
  Znth i l 0 <> 0 ->
  count = array_count_zero_spec (sublist 0 i l) ->
  ... |-- count =
          array_count_zero_spec (sublist 0 (i + 1) l)

array_count_zero_entail_wit_3:
  i >= n_pre -> 0 <= i -> i <= n_pre ->
  count = array_count_zero_spec (sublist 0 i l) ->
  Zlength l = n_pre ->
  ... |-- i = n_pre /\ count = array_count_zero_spec l
```

The closest existing proof pattern is `examples/array_count_even/coq/generated/array_count_even_proof_manual.v`. For this task the reusable helper lemmas are simpler:

```coq
Lemma array_count_zero_spec_app_single :
  forall (l : list Z) (x : Z),
    array_count_zero_spec (l ++ x :: nil) =
    array_count_zero_spec l + (if Z.eq_dec x 0 then 1 else 0).

Lemma array_count_zero_spec_bounds :
  forall (l : list Z),
    0 <= array_count_zero_spec l <= Zlength l.
```

`array_count_zero_spec_app_single` handles both branch witnesses after rewriting `sublist 0 (i + 1) l` as `sublist 0 i l ++ [Znth i l 0]`. `array_count_zero_spec_bounds` proves the accumulator range needed before `count++`; combined with `Zlength_sublist`, `i < n_pre`, and the local integer range fact for variable `n`, it gives `count + 1 <= INT_MAX`. The initialization and exit witnesses should then close with `entailer!`, `sublist_self`, and `lia`.

## 2026-04-22 final proof compile result

The planned edit was applied in `coq/generated/array_count_zero_proof_manual.v`:

```coq
Lemma array_count_zero_spec_app_single : ...
Lemma array_count_zero_spec_bounds : ...

Lemma proof_of_array_count_zero_safety_wit_4 : array_count_zero_safety_wit_4.
Lemma proof_of_array_count_zero_entail_wit_1 : array_count_zero_entail_wit_1.
Lemma proof_of_array_count_zero_entail_wit_2_1 : array_count_zero_entail_wit_2_1.
Lemma proof_of_array_count_zero_entail_wit_2_2 : array_count_zero_entail_wit_2_2.
Lemma proof_of_array_count_zero_entail_wit_3 : array_count_zero_entail_wit_3.
```

The full compile replay succeeded for `original/array_count_zero.v`, `array_count_zero_goal.v`, `array_count_zero_proof_auto.v`, `array_count_zero_proof_manual.v`, and `array_count_zero_goal_check.v` under logical prefix `SimpleC.EE.CAV.verify_20260422_034412_array_count_zero`. A grep for `Admitted.` and top-level `Axiom` in `array_count_zero_proof_manual.v` returned no matches. After compilation, non-`.v` artifacts under workspace `coq/` were removed.
