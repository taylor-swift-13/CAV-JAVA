## Manual proof iteration 1

Fresh `symexec` succeeded on `annotated/verify_20260422_212943_reverse_copy.c` and generated three manual obligations:

```coq
Lemma proof_of_reverse_copy_entail_wit_1 : reverse_copy_entail_wit_1.
Lemma proof_of_reverse_copy_entail_wit_2 : reverse_copy_entail_wit_2.
Lemma proof_of_reverse_copy_return_wit_1 : reverse_copy_return_wit_1.
```

The relevant generated loop-preservation goal has this heap update on the left:

```coq
IntArray.full dst_pre n_pre
  (replace_Znth i (Znth (n_pre - 1 - i) ls 0)
    (app (rev (sublist (n_pre - i) n_pre ls))
         (sublist i n_pre ld)))
```

and must prove the next invariant shape:

```coq
IntArray.full dst_pre n_pre
  (app (rev (sublist (n_pre - (i + 1)) n_pre ls))
       (sublist (i + 1) n_pre ld))
```

This is semantically provable from `0 <= i < n_pre`, `Zlength ls = n_pre`, and `Zlength ld = n_pre`. The proof should not change the annotation: all heap ownership and loop-state facts are present, and the remaining work is pure list normalization.

Planned edit in `reverse_copy_proof_manual.v`:

```coq
Lemma Zlength_rev_Z ...
Lemma reverse_copy_replace_Znth ...
```

The helper will split the source suffix

```coq
sublist (n - (i + 1)) n ls =
  sublist (n - 1 - i) (n - i) ls ++ sublist (n - i) n ls
```

so `rev` turns it into the old written prefix plus the newly copied element. It will also split the destination suffix at `i`, rewrite the `replace_Znth` at offset `0`, and leave the untouched suffix as `sublist (i + 1) n ld`.

Expected witness scripts:

```coq
entail_wit_1: pre_process; normalize empty reverse prefix and whole old destination; entailer!.
entail_wit_2: pre_process; rewrite reverse_copy_replace_Znth; entailer!.
return_wit_1: pre_process; derive i = n_pre; normalize sublist 0 n ls and empty dst suffix; entailer!.
```

## Manual proof iteration 2

The first compile attempt failed in `reverse_copy_proof_manual.v` at the local helper:

```text
File ".../reverse_copy_proof_manual.v", line 51, characters 44-47:
Error: Tactic failure: Cannot find witness.
```

The failing command was:

```coq
rewrite (sublist_split i n (i + 1) ld) by lia.
```

`sublist_split` states its upper-bound side condition using `Z.of_nat (length ld)`, while the generated VC context gives `Zlength ld = n`. Plain `lia` did not unfold this bridge. The proof already has `Hld : Zlength ld = n`, so the fix is to solve these side conditions with:

```coq
rewrite <- Zlength_correct; lia
```

The same issue applies to the source-side split over `ls`. This is a proof-only side-condition fix; the witness body and annotation remain unchanged.

The next compile showed that this environment's selected `sublist_split` side condition was already expressed in a shape where `rewrite <- Zlength_correct` had no matching subterm:

```text
Found no subterm matching "Z.of_nat (Datatypes.length ?M3045)" in the current goal.
```

I will instead solve the side condition by posing the conversion fact without rewriting blindly:

```coq
pose proof (Zlength_correct ld); lia
```

and similarly for `ls`.

The following compile advanced to the source-side one-element split, then failed because `sublist_single` expects the upper bound syntactically as `start + 1`:

```text
Found no subterm matching "sublist (n - 1 - i) (n - 1 - i + 1) ls"
```

The current term is equivalent but printed as:

```coq
sublist (n - 1 - i) (n - i) ls
```

The next edit avoids relying on syntactic matching by replacing that exact sublist with the singleton list in a separate `replace ... with ...` block, and proving the replacement using `sublist_single`.

The next compile reduced the source split but left the destination write as:

```coq
rev old ++ replace_Znth 0 x (old_head :: suffix)
```

while the right side was:

```coq
(rev old ++ x :: nil) ++ suffix
```

These are definitionally equal after unfolding `replace_Znth` at `0` and reassociating append. I will add `unfold replace_Znth; simpl; rewrite <- app_assoc; simpl`.

## Manual proof completion

After unfolding `replace_Znth` and reassociating append, the complete compile replay succeeded:

```text
coqc reverse_copy_goal.v
coqc reverse_copy_proof_auto.v
coqc reverse_copy_proof_manual.v
coqc reverse_copy_goal_check.v
```

The final `reverse_copy_proof_manual.v` contains no `Admitted.`, no top-level `Axiom`, and no `Parameter`. The local proof-only helper lemmas are:

```coq
Lemma Zlength_rev_Z : forall (l : list Z), Zlength (rev l) = Zlength l.
Lemma reverse_copy_replace_Znth : ...
```

`reverse_copy_replace_Znth` is used only by `proof_of_reverse_copy_entail_wit_2`; the initialization and return witnesses close by normalizing empty/full `sublist` expressions and then calling `entailer!`.
