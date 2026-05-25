# Verification Issues

## Issue 1: Loop needed an explicit current-array invariant

- Phenomenon: the active annotated C initially copied the input exactly and had no `Inv` before `for (i = 0; i < n; ++i)`. For this in-place update, symexec would not have a persistent logical list for the current contents of `a`, nor a relation between processed indices and the original list `l`.
- Trigger: the target postcondition requires an existential `l0` such that every original negative element becomes `0` and every original nonnegative element is preserved.
- Fix action: added an invariant in `annotated/verify_20260422_023444_array_clamp_nonnegative.c` with existential `lc`:

```c
/*@ Inv exists lc,
      0 <= i && i <= n@pre &&
      n == n@pre &&
      a == a@pre &&
      n@pre == Zlength(l) &&
      Zlength(lc) == n@pre &&
      (forall (k: Z), (0 <= k && k < i && l[k] < 0) => lc[k] == 0) &&
      (forall (k: Z), (0 <= k && k < i && l[k] >= 0) => lc[k] == l[k]) &&
      (forall (k: Z), (i <= k && k < n@pre) => lc[k] == l[k]) &&
      IntArray::full(a, n@pre, lc)
*/
```

- Result: running `QualifiedCProgramming/linux-binary/symexec` with explicit output paths completed successfully and generated fresh `array_clamp_nonnegative_goal.v`, `array_clamp_nonnegative_proof_auto.v`, `array_clamp_nonnegative_proof_manual.v`, and `array_clamp_nonnegative_goal_check.v`.

## Issue 2: Manual proof needed local `replace_Znth` index lemmas

- Phenomenon: `coq/generated/array_clamp_nonnegative_proof_manual.v` initially contained three admitted lemmas:

```coq
Lemma proof_of_array_clamp_nonnegative_entail_wit_2_1 : array_clamp_nonnegative_entail_wit_2_1.
Proof. Admitted.

Lemma proof_of_array_clamp_nonnegative_entail_wit_2_2 : array_clamp_nonnegative_entail_wit_2_2.
Proof. Admitted.

Lemma proof_of_array_clamp_nonnegative_entail_wit_3 : array_clamp_nonnegative_entail_wit_3.
Proof. Admitted.
```

- Localization: `array_clamp_nonnegative_entail_wit_2_1` is the true branch after writing `a[i] = 0`; it must prove the next invariant over `replace_Znth i 0 lc_2`. This required proving that `Znth i` of the replaced list is the new value and that other indices are unchanged.
- Fix action: added local helper lemmas for `length_replace_nth`, `nth_replace_nth_same`, `nth_replace_nth_diff`, `Zlength_replace_Znth`, `Znth_replace_Znth_same`, and `Znth_replace_Znth_diff`. The diff helper includes an explicit `0 <= i` premise so `Z.to_nat k <> Z.to_nat i` follows from `k <> i`.
- Result: the three manual witnesses were completed without `Admitted.` or any new `Axiom`.

## Issue 3: `entailer!` bullet order did not match source assertion order

- Phenomenon: after `Exists (replace_Znth i 0 lc_2); entailer!.` in `proof_of_array_clamp_nonnegative_entail_wit_2_1`, the first attempted bullet tried to rewrite `Zlength (replace_Znth ...)`, but Coq reported:

```text
Found no subterm matching "Zlength (replace_Znth ?M8920 ?M8921 ?M8922)" in the current goal.
```

- Localization: `coqtop` showed the actual post-`entailer!` goals were ordered as suffix relation, nonnegative prefix relation, negative prefix relation, then length:

```text
goal 1: forall k_3, i + 1 <= k_3 < n_pre -> ...
goal 2: forall k_2, 0 <= k_2 < i + 1 /\ Znth k_2 l 0 >= 0 -> ...
goal 3: forall k, 0 <= k < i + 1 /\ Znth k l 0 < 0 -> ...
goal 4: Zlength (replace_Znth i 0 lc_2) = n_pre
```

- Fix action: reordered the proof bullets for `entail_wit_2_1`; inspected and reordered `entail_wit_2_2` similarly. In `entail_wit_3`, `entailer!` solved all goals after `i = n_pre`, so the explicit bullets were removed after Coq reported `Wrong bullet -: No more goals`.
- Result: the full compile template passed through `array_clamp_nonnegative_goal_check.v`.
