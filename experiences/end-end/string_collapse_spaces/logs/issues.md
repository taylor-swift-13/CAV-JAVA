## Ghost `n@pre` in contract blocked parsing

- Phenomenon: the first `symexec` run failed before symbolic execution of the body:

```text
fatal error: Expected C expression in .../annotated/verify_20260422_224852_string_collapse_spaces.c:23:1
Now parsing : n with type :2
```

- Trigger: `input/string_collapse_spaces.c` uses `n@pre` in `Ensure`, but `n` is a ghost variable from `With l d n`, not a C variable. The front end accepts `@pre` on real C parameters in examples, but here it tried to parse ghost `n@pre` as a C pre-state expression.
- Fix action: left `input/` untouched and normalized only the active annotated copy by replacing ghost `n@pre` with ghost `n` in the contract and annotations. This is semantically equivalent because `n` is not assigned by the C program, but it is still a Contract-stage syntax defect in the original input.
- Result: `symexec` progressed into `string_collapse_spaces`.

## `sublist` in string invariant was rejected

- Phenomenon: after `n@pre` normalization, `symexec` failed at the loop invariant:

```text
fatal error: Use of undeclared identifier `sublist'
```

- Triggering annotation fragment:

```c
j == Zlength(string_collapse_spaces_spec(sublist(0, i, l))) &&
lout[p] == string_collapse_spaces_spec(sublist(0, i, l))[p]
```

- Fix action: rewrote the invariant to the string-example prefix/suffix form:

```c
exists lin lrest dout,
  l == app(lin, lrest) &&
  Zlength(lin) == i &&
  j == Zlength(string_collapse_spaces_spec(lin)) &&
  CharArray::full(out, n + 1, app(string_collapse_spaces_spec(lin), dout))
```

- Result: the front end no longer reported `sublist` as undeclared.

## Disjunctions in invariant caused loop assertion mismatch

- Phenomenon: `symexec` failed while matching current assertions to the loop invariant:

```text
fatal error: The number of now assertions and loop inv pre assertions does not match.
```

- Triggering annotation fragment:

```c
(in_space == 0 || in_space == 1) &&
(in_space == 0 => (i == 0 || l[i - 1] != 32)) &&
```

- Fix action: flattened the disjunctions into an integer range and guarded implication:

```c
0 <= in_space && in_space <= 1 &&
(in_space == 0 && 0 < i => l[i - 1] != 32) &&
```

- Result: `symexec` progressed past invariant parsing.

## Post-loop assertion broke local cleanup

- Phenomenon: the explicit exit assertion before `out[j] = 0` caused:

```text
fatal error: Error: Fail to Remove Memory Permission of in_space:90
```

- Trigger: the assertion omitted the local variable `in_space` and was placed after loop exit, matching the known failure mode where a late exit assertion interferes with local cleanup.
- Fix action: removed the post-loop assertion and relied on the loop invariant plus the branch condition `s[i] == 0` to generate the return witness.
- Result: `symexec` completed successfully:

```text
End of symbolic execution of function string_collapse_spaces
Successfully finished symbolic execution
symexec_status=0
```

## Manual proof incomplete at external time boundary

- Phenomenon: fresh VCs generated five manual obligations. I completed `proof_of_string_collapse_spaces_entail_wit_1`, added local helper lemmas for collapse-spec snoc behavior, and verified that `goal.v`, `proof_auto.v`, and `proof_manual.v` compile while the remaining obligations are still admitted.
- Remaining admitted obligations:

```text
proof_of_string_collapse_spaces_entail_wit_2_1
proof_of_string_collapse_spaces_entail_wit_2_2
proof_of_string_collapse_spaces_entail_wit_2_3
proof_of_string_collapse_spaces_return_wit_1
```

- Current blocker: the remaining witnesses require list/heap normalization around `replace_Znth j ... (string_collapse_spaces_spec lin ++ dout)`, proving the next input prefix is `lin ++ [current]`, and proving on return that `i = n` from the observed terminator and the no-interior-zero contract fact.
- Result: verification is not complete. `goal_check.v` was not compiled after completing all manual proofs because `proof_manual.v` still contains `Admitted.`.

## Retry proof attempt reached branch cleanup goals but did not finish

- Phenomenon: this retry added helper lemmas for `replace_Znth` at an append boundary and for converting previous-character `Znth` facts into `string_collapse_spaces_spec` snoc facts. The helper lemmas compile, but the manual witnesses remain unfinished.
- Triggering theorem: `proof_of_string_collapse_spaces_entail_wit_2_1` in `coq/generated/string_collapse_spaces_proof_manual.v`.
- Stable proof state reached: after destructing `lrest_2 = 32 :: xs` and `dout_2 = y :: ys`, the branch fact was available:

```coq
Hemit :
  string_collapse_spaces_spec (lin_2 ++ [32]) =
  string_collapse_spaces_spec lin_2 ++ [32]
```

The remaining cleanup goals included:

```coq
Zlength (lin_2 ++ [32]) = i + 1
lin_2 ++ 32 :: xs = (lin_2 ++ [32]) ++ xs
1 = 1 -> 0 < i + 1 /\ Znth (i + 1 - 1) (lin_2 ++ 32 :: xs) 0 = 32
Zlength (string_collapse_spaces_spec lin_2) + 1 =
  Zlength (string_collapse_spaces_spec (lin_2 ++ [32]))
```

- Fix attempted: added local lemmas `sccs_replace_Znth_at_app`, `sccs_last_Znth`, `sccs_spec_snoc_space_emit_by_Znth`, and `sccs_spec_snoc_space_suppress_by_Znth`; then attempted to complete `entail_wit_2_1` with explicit `Exists`.
- Result: the partial theorem body was restored to `Admitted.` so `proof_manual.v` stays compilable for the next retry. Verification remains incomplete with four admitted witnesses: `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_2_3`, and `return_wit_1`.

## Retry completed manual witnesses and goal check

- Phenomenon: the retry started with four remaining generated manual placeholders in `coq/generated/string_collapse_spaces_proof_manual.v`:

```coq
proof_of_string_collapse_spaces_entail_wit_2_1
proof_of_string_collapse_spaces_entail_wit_2_2
proof_of_string_collapse_spaces_entail_wit_2_3
proof_of_string_collapse_spaces_return_wit_1
```

- Main proof blockers and fixes:
  - `entail_wit_2_1`: the current space/write branch needed explicit witnesses `lin_2 ++ [32]`, the tail of `lrest_2`, and the tail of `dout_2`; the proof derives `i < n`, splits `lrest_2 = 32 :: xs`, proves the output suffix is nonempty from `CharArray.full_length`, applies `sccs_spec_snoc_space_emit_by_Znth`, and normalizes `replace_Znth` with `sccs_replace_Znth_at_app`.
  - `entail_wit_2_2`: the repeated-space branch needed `in_space = 1`, the previous-character fact from the invariant, and `sccs_spec_snoc_space_suppress_by_Znth`; it keeps `dout_2` unchanged.
  - `entail_wit_2_3`: the non-space branch mirrors `entail_wit_2_1`, but exposes the current input head `cur`, proves `cur <> 32`, applies `sccs_spec_snoc_nonspace`, and rewrites the generated store value `Znth i (l ++ [0]) 0` to `cur`.
  - `return_wit_1`: the return proof first derives `i = n` from `Znth i (l ++ [0]) 0 = 0` plus the no-interior-zero contract, then proves `lrest = nil`, rewrites `l = lin`, destructs the nonempty output suffix, and normalizes the final `replace_Znth j 0`.
- Representative proof pitfalls fixed during the retry:

```coq
(* Bracket tactic forms parsed badly under the generated notation stack. *)
destruct (Z.eq_dec i n) as [Hi_eq | Hi_neq].  (* then use bullets *)

(* CharArray.full_length gives a Z.of_nat length fact; bridge to Zlength first. *)
assert (Hout_len: Zlength (replace_Znth ...) = n + 1).
{ rewrite Zlength_correct. exact H20. }

(* Final entailer goals came in a different order than expected; the no-zero
   forall goals must be solved before previous-character and length goals. *)
```

- Result: the full chain compiled:

```text
coqc original/string_collapse_spaces.v
coqc coq/generated/string_collapse_spaces_goal.v
coqc coq/generated/string_collapse_spaces_proof_auto.v
coqc coq/generated/string_collapse_spaces_proof_manual.v
coqc coq/generated/string_collapse_spaces_goal_check.v
```

`coq/generated/string_collapse_spaces_proof_manual.v` has no `Admitted.` placeholders and no newly introduced `Axiom`. The workspace `coq/` non-`.v` artifacts and `input/` non-`.c`/non-`.v` artifacts were cleaned after compilation.
