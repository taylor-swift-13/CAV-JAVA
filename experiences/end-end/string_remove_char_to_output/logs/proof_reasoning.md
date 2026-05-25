## 2026-04-23 proof pass 1

Fresh `symexec` completed successfully after active-copy postcondition normalization and generated the current manual proof file:

```text
coq/generated/string_remove_char_to_output_proof_manual.v
```

The manual file contains five admitted obligations:

```coq
proof_of_string_remove_char_to_output_entail_wit_1
proof_of_string_remove_char_to_output_entail_wit_2_1
proof_of_string_remove_char_to_output_entail_wit_2_2
proof_of_string_remove_char_to_output_entail_wit_3
proof_of_string_remove_char_to_output_return_wit_1
```

I inspected the current `goal.v`. The witness meanings are:

- `entail_wit_1`: initialize the loop invariant with `l1 = nil`, `l2 = l`, and `d1 = d`.
- `entail_wit_2_1`: nonmatching branch after `out[j] = s[i]`; expose the current suffix head, normalize the output `replace_Znth`, and prove the filtered spec grows by one kept character.
- `entail_wit_2_2`: matching branch with no output write; expose the current suffix head and prove the filtered spec drops that character.
- `entail_wit_3`: loop-exit assertion; prove `i = n` from `s[i] == 0` and the no-internal-zero contract, then split the output suffix into `x :: t`.
- `return_wit_1`: after `out[j] = 0`, normalize `replace_Znth` at the end of the filtered prefix and instantiate the postcondition suffix with `t_2`.

The generated VC shape matches the archived same-program proof pattern: the hard parts are pure list/spec append facts and `replace_Znth` at an append boundary, not missing heap ownership. I will add local helper lemmas before the generated witness proofs:

```coq
Lemma string_remove_char_to_output_spec_app : ...
Lemma string_remove_char_to_output_spec_keep_single : ...
Lemma string_remove_char_to_output_spec_drop_single : ...
Lemma string_remove_char_to_output_spec_zlength_le : ...
Lemma current_head_after_prefix : ...
Lemma replace_at_prefix_end : ...
```

These helpers correspond directly to the current goals: the keep/drop lemmas prove the recursive Coq spec over `l1 ++ [x]`; `current_head_after_prefix` connects the C read index to the head of `l2`; `replace_at_prefix_end` rewrites the output heap after writing at index `j = Zlength(filtered_prefix)`. The witness scripts will use `pre_process`, explicit destructs of the input/output suffixes when needed, `Exists` for QCP existentials, and `entailer!` plus `lia` for the remaining arithmetic.
