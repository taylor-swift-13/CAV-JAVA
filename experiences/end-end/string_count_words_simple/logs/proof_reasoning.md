# Proof Reasoning

## Initial manual witness plan

Fresh `symexec` succeeded on the active annotated file and generated five manual entailment witnesses:

```coq
proof_of_string_count_words_simple_entail_wit_1
proof_of_string_count_words_simple_entail_wit_2_1
proof_of_string_count_words_simple_entail_wit_2_2
proof_of_string_count_words_simple_entail_wit_2_3
proof_of_string_count_words_simple_entail_wit_3
```

The generated invariant is prefix-based:

```coq
count = string_count_words_simple_spec (sublist 0 i l)
```

The three loop-body preservation witnesses correspond to these C branches:

```c
if (s[i] == 32) {
    in_word = 0;
} else {
    if (!in_word) {
        count++;
        in_word = 1;
    }
}
i++;
```

The proof needs to show how `string_count_words_simple_spec (sublist 0 i l)` changes when the next character is appended to the processed prefix. The reusable list facts needed are:

```coq
sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0]
```

under `0 <= i < Zlength l`, plus three word-count facts:

```coq
string_count_words_simple_spec (p ++ [32]) =
  string_count_words_simple_spec p

x <> 32 ->
string_count_words_simple_spec ([x]) =
  string_count_words_simple_spec [] + 1

y <> 32 -> x <> 32 ->
string_count_words_simple_spec ((p ++ [y]) ++ [x]) =
  string_count_words_simple_spec (p ++ [y])

x <> 32 ->
string_count_words_simple_spec ((p ++ [32]) ++ [x]) =
  string_count_words_simple_spec (p ++ [32]) + 1
```

Witness `entail_wit_2_1` is the space branch. It should prove `count` is unchanged when the current character `x` is `32`.

Witness `entail_wit_2_2` is the non-space branch with `in_word = 0`. If `i = 0`, the processed prefix is empty and the non-space character starts the first word. If `0 < i`, the invariant says the previous character is `32`, so appending the current non-space character starts one new word.

Witness `entail_wit_2_3` is the non-space branch with `in_word <> 0`. The bounds `0 <= in_word <= 1` imply `in_word = 1`, and the invariant then says the previous character is non-space; appending another non-space character continues the current word and does not change `count`.

Witness `entail_wit_3` is the loop-exit assertion. It must derive `i = n` from `Znth i (l ++ [0]) 0 = 0`, `0 <= i <= n`, and the contract fact that all `l[k]` for `0 <= k < n` are nonzero. After `i = n`, `sublist 0 i l = l`, so the invariant gives the required final count.

## Proof iterations and final script shape

The first manual script used helper lemmas but initially failed in Coq before any witness proof because `sublist_split` and `sublist_single` expect side conditions over `Z.of_nat (length l)`, while the local facts are stated with `Zlength l`. The helper was fixed by adding `pose proof (Zlength_correct l)` in the side-condition proofs:

```coq
rewrite (sublist_split 0 (i + 1) i l)
  by (pose proof (Zlength_correct l); lia).
rewrite (sublist_single i l d)
  by (pose proof (Zlength_correct l); lia).
```

The generated `Local Open Scope sac` made richer intro-pattern syntax brittle in helper proofs, so the induction proofs were written in the simpler generated-file style:

```coq
induction l.
...
destruct (Z.eq_dec a 32).
```

The semantic helper lemmas finally used in `proof_manual.v` are:

```coq
sublist_prefix_snoc_Z
string_count_words_simple_go_app_space
string_count_words_simple_spec_app_space
string_count_words_simple_spec_single_nonspace
string_count_words_simple_go_app_space_nonspace
string_count_words_simple_spec_app_space_nonspace
string_count_words_simple_go_app_nonspace_nonspace
string_count_words_simple_spec_app_nonspace_nonspace
```

Representative failed compile errors and fixes:

```text
Error: Tactic failure: Cannot find witness.
```

This occurred when `lia` did not solve a branch after rewriting the terminator index. For equality-to-space exits, the proof now uses `discriminate`; for nonzero contradictions, it explicitly applies the `<> 0` hypothesis to `reflexivity`.

```text
Error: Attempt to save an incomplete proof
```

For `entail_wit_2_1` and `entail_wit_2_2`, `entailer!` left branch-state implications such as:

```coq
0 < i + 1 /\ 0 = 0 -> Znth (i + 1 - 1) l 0 = 32
in_word = 1 -> 0 < i + 1 /\ Znth (i + 1 - 1) l 0 <> 32
```

The final proof discharges these by asserting the exact implication before `entailer!`, using the current-character facts obtained from the branch condition.

```text
Error: Found no subterm matching "sublist 0 ? ?"
```

In the exit witness, the remaining `sublist 0 n l` occurrence was in hypothesis `H7`, not in the goal. The final proof rewrites `sublist_self` in `H7` and then lets `entailer!` close the assertion.

Final compile result: `original/string_count_words_simple.v`, generated `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled successfully. `proof_manual.v` contains no `Admitted.` and no new `Axiom`.
