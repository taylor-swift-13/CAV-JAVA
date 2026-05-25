## 2026-04-23 proof iteration 1: generated manual witnesses

Fresh `symexec` on `annotated/verify_20260423_021759_string_equal.c` succeeded with status 0 and generated six manual obligations in `coq/generated/string_equal_proof_manual.v`:

```coq
Lemma proof_of_string_equal_entail_wit_1 : string_equal_entail_wit_1.
Lemma proof_of_string_equal_entail_wit_2 : string_equal_entail_wit_2.
Lemma proof_of_string_equal_return_wit_1 : string_equal_return_wit_1.
Lemma proof_of_string_equal_return_wit_2 : string_equal_return_wit_2.
Lemma proof_of_string_equal_return_wit_3 : string_equal_return_wit_3.
Lemma proof_of_string_equal_return_wit_4 : string_equal_return_wit_4.
```

`entail_wit_1` is loop invariant initialization. The target existential is `EX lb1 lb2 la1 la2`; the proof should instantiate `lb1 = nil`, `lb2 = lb`, `la1 = nil`, and `la2 = la`, then let `entailer!` discharge the vacuous prefix equality and preserved heap resources.

`entail_wit_2` is loop invariant preservation after the body reaches `i++`. The VC has:

```coq
Znth i (la ++ 0 :: nil) 0 = Znth i (lb ++ 0 :: nil) 0
Znth i (lb ++ 0 :: nil) 0 <> 0
Znth i (la ++ 0 :: nil) 0 <> 0
0 <= i, i <= na, i <= nb
la = la1_2 ++ la2_2
lb = lb1_2 ++ lb2_2
Zlength la1_2 = i
Zlength lb1_2 = i
```

The proof needs to show `i + 1 <= na` and `i + 1 <= nb`, split each suffix into a head character and tail, then instantiate the next invariant prefixes as `la1_2 ++ x :: nil` and `lb1_2 ++ y :: nil`. The useful reusable bridge is: if `Zlength l = n`, `0 <= i <= n`, and `Znth i (l ++ [0]) 0 <> 0`, then `i < n`; otherwise `i = n` would read the appended terminator.

The return witnesses are all postcondition case splits:

```coq
return_wit_1: mismatch before either terminator, choose the existential mismatch case with k = i.
return_wit_2: both reads are zero, choose the successful equality case.
return_wit_3: a[i] is zero and b[i] is nonzero, choose length-difference case.
return_wit_4: a[i] is nonzero and b[i] is zero, choose length-difference case.
```

The second reusable bridge is: if `Zlength l = n`, `0 <= i <= n`, all `l[0..n)` are nonzero, and `Znth i (l ++ [0]) 0 = 0`, then `i = n`. This converts the loop-exit reads into `i = na` or `i = nb`; the prefix equality invariant then covers all `k < na` in the successful return branch.

## 2026-04-23 proof iteration 2: after simplifying invariant

After annotation iteration 2 and fresh `symexec`, the manual file no longer contained `entail_wit_1`; the remaining witnesses were:

```coq
proof_of_string_equal_entail_wit_2
proof_of_string_equal_return_wit_1
proof_of_string_equal_return_wit_2
proof_of_string_equal_return_wit_3
proof_of_string_equal_return_wit_4
```

The final proof adds two local helper lemmas in `coq/generated/string_equal_proof_manual.v`:

```coq
string_equal_nonzero_index_lt :
  Zlength l = n ->
  0 <= i -> i <= n ->
  Znth i (l ++ 0 :: nil) 0 <> 0 ->
  i < n.

string_equal_zero_index_eq :
  Zlength l = n ->
  0 <= i -> i <= n ->
  (forall k, 0 <= k < n -> Znth k l 0 <> 0) ->
  Znth i (l ++ 0 :: nil) 0 = 0 ->
  i = n.
```

`entail_wit_2` uses the first helper twice to derive `i < na` and `i < nb`, rewrites the branch equality from `Znth i (la ++ [0])` / `Znth i (lb ++ [0])` to `Znth i la` / `Znth i lb`, and proves the extended prefix equality by splitting `k < i + 1` into `k < i` and `k = i`.

The return witnesses use assertion-level disjunction tactics. Because the generated postcondition is left-associated as `(length_diff || mismatch_exists) || success`, the mismatch branch is selected with `Left; Right`, the length-difference branch with `Left; Left`, and the success branch with `Right`. `return_wit_2` uses `string_equal_zero_index_eq` for both arrays to prove `na = nb`, then reuses the invariant prefix equality for every `k < na`. `return_wit_3` and `return_wit_4` combine one zero-index equality and one nonzero-index strict bound to prove `na <> nb`.

Final compile result: `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compile under the documented template. `proof_manual.v` contains no `Admitted.` and no newly introduced `Axiom`.
