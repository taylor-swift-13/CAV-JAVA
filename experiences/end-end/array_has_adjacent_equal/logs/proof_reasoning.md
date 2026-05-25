## 2026-04-22T05:03:00+08:00 - Manual return witness for zero result

Fresh `symexec` succeeded on the current annotated file and generated one manual obligation:

```coq
Lemma proof_of_array_has_adjacent_equal_return_wit_2 :
  array_has_adjacent_equal_return_wit_2.
Proof. Admitted.
```

The generated goal is the return-0 postcondition entailment. Its precondition contains the loop-exit guard fact and invariant facts:

```coq
[| (i_3 >= n_pre) |] &&
[| (1 <= i_3) |] &&
[| (i_3 <= (n_pre + 1)) |] &&
[| forall j,
     1 <= j /\ j < i_3 ->
     Znth j l 0 <> Znth (j - 1) l 0 |] &&
IntArray.full a_pre n_pre l
|--
  ([| forall i,
       1 <= i /\ i < n_pre ->
       Znth i l 0 <> Znth (i - 1) l 0 |] &&
   IntArray.full a_pre n_pre l)
  || ...
```

The intended proof should choose the left disjunct with assertion-level `Left`, keep the unchanged `IntArray.full` heap via `entailer!`, and prove the universal postcondition by applying the invariant universal. For any target `i`, the postcondition gives `i < n_pre`, while loop exit gives `i_3 >= n_pre`; therefore `i < i_3` by arithmetic. No helper lemma is needed; the only nontrivial step is a pure arithmetic bridge from `i < n_pre` and `n_pre <= i_3` to `i < i_3`.

Planned proof skeleton:

```coq
Proof.
  pre_process.
  Left.
  entailer!.
  intros i [? ?].
  match goal with
  | H : forall j, 1 <= j /\ j < _ -> _ |- _ =>
      apply H; lia
  end.
Qed.
```
