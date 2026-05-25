## 2026-04-22 16:27:04 +0800 - Manual proof obligations after symbol-collision repair

After renaming the C implementation symbol in the active annotated copy from `factorial` to `fac`, `symexec` succeeded and generated:

- `output/verify_20260422_161944_factorial/coq/generated/factorial_goal.v`
- `output/verify_20260422_161944_factorial/coq/generated/factorial_proof_auto.v`
- `output/verify_20260422_161944_factorial/coq/generated/factorial_proof_manual.v`
- `output/verify_20260422_161944_factorial/coq/generated/factorial_goal_check.v`

The manual file currently has three unfinished lemmas:

```coq
Lemma proof_of_fac_safety_wit_3 : fac_safety_wit_3.
Proof. Admitted.

Lemma proof_of_fac_entail_wit_1 : fac_entail_wit_1.
Proof. Admitted.

Lemma proof_of_fac_entail_wit_3 : fac_entail_wit_3.
Proof. Admitted.
```

The corresponding witness names are:

- `fac_safety_wit_3`: overflow bound for `res = res * i` when `1 <= i <= n_pre <= 10` and `res = factorial(i - 1)`.
- `fac_entail_wit_1`: loop invariant initialization, including the base fact `1 = factorial(1 - 1)`.
- `fac_entail_wit_3`: bridge from the C assignment result `(factorial (i - 1)) * i` to the post-assignment assertion `factorial i`.

The generated `fac_entail_wit_3` goal in `factorial_goal.v` requires turning the heap cell:

```coq
((( &( "res" ) )) # Int  |-> ((factorial ((i - 1 ))) * i ))
```

into:

```coq
((( &( "res" ) )) # Int  |-> (factorial (i)))
```

under `1 <= i`; this is exactly the recurrence `factorial_inc` after rewriting `i` as `(i - 1) + 1`.

The generated `fac_safety_wit_3` goal only needs bounded arithmetic facts for all possible `i` in `1..10`. The archived successful proof at `./archieve/output_backup_20260422_011624/verify_20260414_153520_factorial/coq/generated/factorial_proof_manual.v` proves this by finite case splitting on `i = 1, ..., 10`, then `vm_compute`.

Plan:

1. Reuse the archived proof bodies for `proof_of_fac_safety_wit_3`, `proof_of_fac_entail_wit_1`, and `proof_of_fac_entail_wit_3`, because the regenerated witness names and goal shapes are the same in this workspace.
2. Keep the current import path `From SimpleC.EE.CAV.verify_20260422_161944_factorial Require Import factorial_goal`.
3. Compile `factorial_goal.v`, `factorial_proof_auto.v`, `factorial_proof_manual.v`, and `factorial_goal_check.v` with the standard workspace load path.
4. If compilation fails, use the concrete `coqc` error and proof state to refine the proof; do not leave `Admitted.` in `factorial_proof_manual.v`.
