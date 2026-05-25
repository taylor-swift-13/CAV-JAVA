## 2026-04-22 09:18:30 +0800 - Initial manual proof plan

Fresh `symexec` succeeded on the current annotated file and generated:

```text
binary_search_goal.v
binary_search_proof_auto.v
binary_search_proof_manual.v
binary_search_goal_check.v
```

`coq/generated/binary_search_proof_manual.v` contains five admitted obligations:

```coq
Lemma proof_of_binary_search_safety_wit_4 : binary_search_safety_wit_4.
Proof. Admitted.

Lemma proof_of_binary_search_entail_wit_1 : binary_search_entail_wit_1.
Proof. Admitted.

Lemma proof_of_binary_search_entail_wit_2 : binary_search_entail_wit_2.
Proof. Admitted.

Lemma proof_of_binary_search_entail_wit_3_1 : binary_search_entail_wit_3_1.
Proof. Admitted.

Lemma proof_of_binary_search_entail_wit_3_2 : binary_search_entail_wit_3_2.
Proof. Admitted.
```

The generated goals show these are pure arithmetic/order obligations plus preservation of `IntArray.full`:

- `safety_wit_4` proves the assignment `mid = left + (right - left) / 2` remains within signed-int bounds. Available facts include `0 <= left`, `left <= right`, `right < n_pre`, and `n_pre <= INT_MAX`.
- `entail_wit_1` proves invariant initialization after `left = 0; right = n - 1`; the quantified eliminated ranges are empty.
- `entail_wit_2` proves the bridge assertion after computing `mid`, especially `0 <= mid`, `mid < n_pre`, `left <= mid`, and `mid <= right`.
- `entail_wit_3_1` preserves the invariant in the `right = mid - 1` branch. The key semantic fact is `Znth mid l 0 >= target_pre` and `Znth mid l 0 <> target_pre`, hence `target_pre < Znth mid l 0`; sortedness gives `Znth mid l 0 <= Znth i l 0` for all `i >= mid`.
- `entail_wit_3_2` preserves the invariant in the `left = mid + 1` branch. The key semantic fact is `Znth mid l 0 < target_pre`; sortedness gives `Znth i l 0 <= Znth mid l 0` for all `i <= mid`.

First proof attempt will use the standard generated-goal skeleton:

```coq
Proof.
  pre_process.
  entailer!.
  lia.
Qed.
```

If this does not solve the quantified preservation goals, I will add explicit `Intros`/`intro` steps and instantiate the sortedness hypothesis with the relevant index pair.

## 2026-04-22 09:19:20 +0800 - First proof failure and adapted `upper_bound` pattern

The first compile attempt with the stable `COMPILE.md` template compiled `binary_search_goal.v`, then failed in `proof_manual.v` at `safety_wit_4`:

```text
File ".../binary_search_proof_manual.v", line 25, characters 2-5:
Error: Tactic failure: Cannot find witness.
```

The failing tactic was:

```coq
Lemma proof_of_binary_search_safety_wit_4 : binary_search_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  lia.
Qed.
```

The goal contains the expression `(right - left) ÷ 2`, so plain `lia` cannot reason about the C-style quotient. I found a close archived proof at:

```text
./archieve/output_backup_20260422_011624/verify_20260421_040514_upper_bound/coq/generated/upper_bound_proof_manual.v
```

It proves:

```coq
Lemma upper_bound_quot2_bounds:
  forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
```

and uses it before `entailer!` for the same midpoint expression. I will add a local `binary_search_quot2_bounds` helper and use it in `safety_wit_4` and `entail_wit_2`.

For the two branch-preservation witnesses, I will follow the same archived pattern:

- In `entail_wit_3_1`, prove a local `Hupper_new` for all `mid <= j < n_pre`. At `j = mid`, `Znth mid l 0 >= target_pre` and `Znth mid l 0 <> target_pre` imply `target_pre < Znth mid l 0`; for `j > mid`, sortedness gives `Znth mid l 0 <= Znth j l 0`.
- In `entail_wit_3_2`, prove a local `Hlower_new` for all `0 <= j < mid + 1`. If `j < left`, reuse the old eliminated-left invariant; otherwise `left <= j <= mid`, and sortedness plus `Znth mid l 0 < target_pre` gives `Znth j l 0 < target_pre`.

Both branch witnesses also need `sep_apply store_int_undef_store_int` because the invariant conclusion changes `mid` from a concrete stored value back to an undefined local cell.

## 2026-04-22 09:20:05 +0800 - Remaining quantified goals after `entailer!`

After adding the quotient helper and branch-local facts, compilation advanced to `entail_wit_3_1` but failed with:

```text
Error: (in proof proof_of_binary_search_entail_wit_3_1): Attempt to save an incomplete proof
```

`coqtop` showed the remaining post-`entailer!` goal:

```coq
Hupper_new : forall j : Z, mid <= j < n_pre -> target_pre < Znth j l 0
============================
forall i_4 : Z, mid - 1 < i_4 < n_pre -> target_pre < Znth i_4 l 0
```

This is not a missing annotation fact; it is just the final invariant quantifier with a syntactically different lower bound. Since `mid - 1 < i_4` is equivalent to `mid <= i_4` over integers, the proof should finish with:

```coq
  entailer!.
  apply Hupper_new; lia.
```

The symmetric `left = mid + 1` branch can leave the same kind of quantified goal, so I will also finish `entail_wit_3_2` with:

```coq
  entailer!.
  apply Hlower_new; lia.
```

## 2026-04-22 09:21:30 +0800 - Manual proof and full `goal_check` succeeded

After changing `entail_wit_3_1` to introduce the remaining quantified index explicitly:

```coq
  entailer!.
  intros i Hi.
  apply Hupper_new; lia.
```

`entail_wit_3_1` compiled. The symmetric extra lines were not needed in `entail_wit_3_2`; `entailer!` solved that witness after `Hlower_new` and `sep_apply store_int_undef_store_int`, so the attempted extra `intros` produced:

```text
Error: No such goal.
```

Removing those two extra lines made `binary_search_proof_manual.v` compile. The full compile replay then succeeded:

```text
compiled=binary_search_goal.v
compiled=binary_search_proof_auto.v
compiled=binary_search_proof_manual.v
compiled=binary_search_goal_check.v
```

Final manual proof checks:

```bash
rg -n "Admitted\\.|^\\s*Axiom\\b" coq/generated/binary_search_proof_manual.v
```

returned no matches.
