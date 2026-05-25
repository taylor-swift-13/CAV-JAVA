## 2026-04-23 issue 1: initial invariant carried unnecessary existential prefix splits

Phenomenon: after the first successful `symexec`, `coq/generated/string_equal_proof_manual.v` contained six manual obligations. The difficult one was `proof_of_string_equal_entail_wit_2`, whose target required constructing fresh witnesses `lb1`, `lb2`, `la1`, and `la2` for the next loop invariant:

```coq
EX lb1 lb2 la1 la2,
  la = la1 ++ la2 /\
  lb = lb1 ++ lb2 /\
  Zlength la1 = i + 1 /\
  Zlength lb1 = i + 1 /\
  forall k, 0 <= k < i + 1 -> Znth k la 0 = Znth k lb 0
```

Trigger: the first annotation used:

```c
/*@ Inv exists la1 la2 lb1 lb2,
      la == app(la1, la2) &&
      lb == app(lb1, lb2) &&
      Zlength(la1) == i &&
      Zlength(lb1) == i &&
      ...
*/
```

Diagnosis: the function never mutates either string. The postcondition needs only direct prefix equality over the original `la` and `lb`, plus full ownership of both arrays. The existential prefix/suffix split created proof work that was not needed for either memory ownership or final semantics.

Fix: replaced the invariant in `annotated/verify_20260423_021759_string_equal.c` with the direct form:

```c
/*@ Inv
      0 <= i && i <= na && i <= nb &&
      a == a@pre &&
      b == b@pre &&
      (forall (k: Z), (0 <= k && k < i) => la[k] == lb[k]) &&
      ...
*/
```

Result: fresh `symexec` succeeded and regenerated a smaller manual proof file with five obligations and no existential invariant-initialization witness.

## 2026-04-23 issue 2: generated three-way disjunction is left-associated

Phenomenon: the first attempt at `return_wit_1` used:

```coq
Right.
Left.
```

`coqc` failed with:

```text
Error: Found no subterm matching "?e || ?e0" in the current goal.
```

Trigger: the postcondition shape is printed as three branches, but the assertion parser associates it as `(length_diff || mismatch_exists) || success`. After `Right`, the selected branch is already the success branch, so there is no remaining disjunction for `Left`.

Fix: selected branches as follows:

```coq
Left; Right.  (* mismatch existential branch *)
Right.        (* success branch *)
Left; Left.   (* length-difference branch *)
```

Result: `return_wit_1`, `return_wit_2`, `return_wit_3`, and `return_wit_4` compiled.

## 2026-04-23 issue 3: string terminator reads need explicit index lemmas

Phenomenon: return witnesses need facts such as `i < na`, `i = na`, `i < nb`, and `i = nb` from reads of `Znth i (l ++ 0 :: nil) 0`. These facts are semantically simple but not solved automatically by `entailer!`.

Fix: added two local helper lemmas to `coq/generated/string_equal_proof_manual.v`:

```coq
string_equal_nonzero_index_lt
string_equal_zero_index_eq
```

The first proves that a nonzero read from `l ++ [0]` at `0 <= i <= n` must have `i < n`; the second proves that a zero read, together with the contract fact that all `l[0..n)` are nonzero, must have `i = n`.

Result: the loop-preservation witness and all return witnesses completed without `Admitted.` or new `Axiom`.
