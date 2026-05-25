## 2026-04-22T18:18:28+08:00 - Manual obligations after fresh symexec

Fresh `symexec` succeeded on the active annotated file and generated two manual obligations in `coq/generated/is_sorted_nondecreasing_proof_manual.v`:

```coq
Lemma proof_of_is_sorted_nondecreasing_safety_wit_2 : is_sorted_nondecreasing_safety_wit_2.
Proof. Admitted.

Lemma proof_of_is_sorted_nondecreasing_return_wit_2 : is_sorted_nondecreasing_return_wit_2.
Proof. Admitted.
```

The first obligation expands to a pure integer range VC:

```coq
Definition is_sorted_nondecreasing_safety_wit_2 :=
forall a_pre n_pre l i,
  [| 0 <= i |] && [| i <= n_pre |] && ... &&
  (((&("i"))) # Int |-> i) ** (((&("n"))) # Int |-> n_pre) ** ...
|-- [| i + 1 <= INT_MAX |] && [| INT_MIN <= i + 1 |].
```

The local `Int` store for `i` should give the C integer representability facts, and the invariant gives `0 <= i`. The planned proof is the standard shortest skeleton `pre_process; entailer!; lia`.

The second obligation is the normal return case:

```coq
Definition is_sorted_nondecreasing_return_wit_2 :=
forall a_pre n_pre l i_3,
  [| i_3 + 1 >= n_pre |] &&
  [| 0 <= i_3 |] &&
  [| i_3 <= n_pre |] &&
  [| forall j, 0 <= j /\ j < i_3 -> Znth j l 0 <= Znth (j + 1) l 0 |] &&
  ... && IntArray.full a_pre n_pre l
|--
  (EX i, [| 1 = 0 |] && ...) ||
  ([| 1 = 1 |] &&
   [| forall i_2, 0 <= i_2 /\ i_2 + 1 < n_pre ->
        Znth i_2 l 0 <= Znth (i_2 + 1) l 0 |] &&
   IntArray.full a_pre n_pre l).
```

This should choose the assertion-level right disjunct with `Right`. For an arbitrary postcondition index `i_2`, the exit condition `i_3 + 1 >= n_pre` and `i_2 + 1 < n_pre` imply `i_2 < i_3`, so the invariant universal can be applied. The planned proof is `pre_process; Right; entailer!; intros; apply H...; lia`, adjusting hypothesis names after compilation if needed.

## 2026-04-22T18:20:00+08:00 - First proof attempt exposed missing guard safety bound

The first manual edit used:

```coq
Lemma proof_of_is_sorted_nondecreasing_safety_wit_2 : is_sorted_nondecreasing_safety_wit_2.
Proof.
  pre_process.
  entailer!.
Qed.
```

Batch replay without fail-fast initially continued after the failure, but `logs/compile_full.log` showed the real error:

```text
Error:
 (in proof proof_of_is_sorted_nondecreasing_safety_wit_2):
 Attempt to save an incomplete proof
```

The `coqtop` state after `entailer!` left `i + 1 <= 2147483647` from only `0 <= i`, `i <= n_pre`, and `0 <= n_pre`. This is not a tactic problem; the annotation lacked the conditional source-level bound needed for `i + 1 < n` guards. I moved back to annotation, added `(0 < n => i + 1 <= n)` to the loop invariant, and reran `symexec` so the witness list is current.

## 2026-04-22T18:21:14+08:00 - Manual proof after conditional-bound invariant

After adding `(0 < n => i + 1 <= n)` and rerunning `symexec`, the manual file now contains only:

```coq
Lemma proof_of_is_sorted_nondecreasing_return_wit_2 : is_sorted_nondecreasing_return_wit_2.
Proof. Admitted.
```

The safety witness moved back to auto-generated proof obligations, confirming that the annotation change fixed the missing loop-guard range fact. The remaining return witness has one extra pure hypothesis:

```coq
[| (0 < n_pre -> i_3 + 1 <= n_pre) |]
```

but the core proof is unchanged. After `pre_process; Right; entailer!; intros`, the invariant universal should be the fourth semantic hypothesis after the exit guard, index bounds, and conditional bound. The proof will use that universal and `lia` to show the arbitrary postcondition index is inside the processed prefix.
