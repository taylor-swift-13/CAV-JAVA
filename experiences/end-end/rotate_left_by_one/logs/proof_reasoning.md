## 2026-04-22 manual proof start

Fresh `symexec` succeeded for the current active annotated file and generated:

```text
coq/generated/rotate_left_by_one_goal.v
coq/generated/rotate_left_by_one_proof_auto.v
coq/generated/rotate_left_by_one_proof_manual.v
coq/generated/rotate_left_by_one_goal_check.v
```

The manual file contains three admitted obligations:

```coq
Lemma proof_of_rotate_left_by_one_entail_wit_1 : rotate_left_by_one_entail_wit_1.
Lemma proof_of_rotate_left_by_one_entail_wit_2 : rotate_left_by_one_entail_wit_2.
Lemma proof_of_rotate_left_by_one_return_wit_1 : rotate_left_by_one_return_wit_1.
```

The generated goals show:

```coq
rotate_left_by_one_entail_wit_1
  initial full array l |-- exists l1, full array app l1 (sublist 0 n l)

rotate_left_by_one_entail_wit_2
  full array after replace_Znth i ... (app l1 (sublist i n l))
  |-- exists l1, full array app l1 (sublist (i+1) n l)

rotate_left_by_one_return_wit_1
  full array after replace_Znth (n-1) first (app l1 (sublist i n l))
  |-- exists lr, rotation postcondition and full array lr
```

These are pure list normalization plus heap predicate framing goals. The archived successful proof for `rotate_left_by_one` has the same invariant shape and supplies two reusable helper lemmas:

```coq
rotate_left_by_one_step_list
rotate_left_by_one_final_list
```

The current contract formats the postcondition as one quantified implication whose consequent is a conjunction of the two index cases, while the archived contract used separate facts. The intended proof is still the same: choose `nil` for initialization, choose `l1 ++ [l[i+1]]` for loop preservation, and choose `l1 ++ [l[0]]` for the return list. I will first transplant the archived proof with the import path already generated for this workspace, then compile; if the final `entailer!` bullet structure differs because of the nested conjunction, I will inspect the failing proof state and adjust only the return witness.
