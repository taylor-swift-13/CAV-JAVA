## 2026-04-22 manual proof round 1

Fresh `symexec` succeeded on the current active annotated file:

```text
End of symbolic execution of function string_collapse_spaces
Successfully finished symbolic execution
symexec_status=0
```

The generated manual file contains five admitted obligations:

```coq
Lemma proof_of_string_collapse_spaces_entail_wit_1 : string_collapse_spaces_entail_wit_1.
Lemma proof_of_string_collapse_spaces_entail_wit_2_1 : string_collapse_spaces_entail_wit_2_1.
Lemma proof_of_string_collapse_spaces_entail_wit_2_2 : string_collapse_spaces_entail_wit_2_2.
Lemma proof_of_string_collapse_spaces_entail_wit_2_3 : string_collapse_spaces_entail_wit_2_3.
Lemma proof_of_string_collapse_spaces_return_wit_1 : string_collapse_spaces_return_wit_1.
```

The first obligation initializes the invariant from the precondition. The witness should instantiate `lin = nil`, `lrest = l`, and `dout = d`, because `string_collapse_spaces_spec nil = nil`, `j = 0`, and the output heap is still exactly the original `d`.

The three `entail_wit_2_*` obligations are the three loop-body cases:

- `entail_wit_2_1`: current char is space and `in_space = 0`; output writes `32`, so the next processed prefix is `lin_2 ++ [32]`, the next `dout` is the tail of the old output suffix, and the collapsed spec length grows by one.
- `entail_wit_2_2`: current char is space and `in_space <> 0`; with `0 <= in_space <= 1`, this means `in_space = 1`, so the output prefix does not grow and `j` stays equal to the collapsed spec length after extending the input prefix by another space.
- `entail_wit_2_3`: current char is nonzero and non-space; output writes that character, so the collapsed spec length grows by one and `in_space` becomes 0.

The return witness must first prove `i = n`: the loop exited with `Znth i (l ++ [0]) 0 = 0`, while the precondition says every `l[k]` for `0 <= k < n` is nonzero. Once `i = n`, the split facts `l = lin ++ lrest` and `Zlength lin = i`, `Zlength l = n` imply `lin = l` and `lrest = nil`; then `replace_Znth j 0 (string_collapse_spaces_spec lin ++ dout)` should normalize to `string_collapse_spaces_spec l ++ [0] ++ tail(dout)`, with `t` instantiated as the tail of `dout`.

Before adding helper lemmas, I will try conservative proof skeletons using `unfold`, `pre_process`, explicit `Exists`, and `entailer!`. If compilation exposes stable pure-list failures, I will add local helper lemmas for `string_collapse_spaces_spec` over `xs ++ [x]`, for splitting a list by `Zlength`, and for `replace_Znth` at the first suffix position.

## 2026-04-22 manual proof round 2

The first compile after adding the `entail_wit_1` skeleton failed:

```text
File ".../string_collapse_spaces_proof_manual.v", line 30, characters 0-4:
Error: (in proof proof_of_string_collapse_spaces_entail_wit_1):
Attempt to save an incomplete proof
```

The skeleton was:

```coq
unfold string_collapse_spaces_entail_wit_1.
intros.
Exists d.
Exists (@nil Z).
Exists l.
entailer!.
```

The missing pure fact is `Zlength d = n + 1`, required by the invariant as `Zlength dout = n + 1 - 0`. The C precondition does not state this directly, but it is implied by the spatial assertion `CharArray.full out_pre (n + 1) d`. The next edit adds `prop_apply CharArray.full_length. Intros.` before the `Exists` steps, matching the pattern used in existing string proofs.

## 2026-04-22 manual proof final state

After simplifying the invariant to remove duplicate suffix-length pure facts and rerunning `symexec`, the generated manual obligations changed but kept the same high-level shape. I completed the initialization witness:

```coq
Lemma proof_of_string_collapse_spaces_entail_wit_1 : string_collapse_spaces_entail_wit_1.
Proof.
  unfold string_collapse_spaces_entail_wit_1.
  pre_process.
  Exists d.
  Exists (@nil Z).
  Exists l.
  entailer!.
Qed.
```

I also added helper lemmas for the remaining proof direction:

```coq
sccs_go_snoc
sccs_end_space_false_last_not
sccs_end_space_true_last
sccs_spec_snoc_nonspace
sccs_spec_snoc_space_emit
sccs_spec_snoc_space_suppress
sccs_replace_Znth_length
```

The file compiles with the four remaining generated `Admitted.` placeholders, but the proof is incomplete. The remaining witnesses need the following facts to be connected inside separation-logic entailments:

- `entail_wit_2_1`: if `in_space = 0` and current char is 32, split `lrest_2` to expose current char, prove `string_collapse_spaces_spec (lin_2 ++ [32]) = string_collapse_spaces_spec lin_2 ++ [32]`, and normalize the output heap after `replace_Znth j 32`.
- `entail_wit_2_2`: if `in_space <> 0`, use `0 <= in_space <= 1` to prove `in_space = 1`, prove the previous processed char was 32, and show appending another 32 does not change the collapsed output prefix.
- `entail_wit_2_3`: for a nonzero non-space char, prove `string_collapse_spaces_spec (lin_2 ++ [x]) = string_collapse_spaces_spec lin_2 ++ [x]` and normalize the output heap after the write.
- `return_wit_1`: prove `i = n` from `Znth i (l ++ [0]) 0 = 0` and the no-interior-zero contract, then show the split prefix `lin` equals `l` and normalize the final `replace_Znth j 0`.

I am stopping at the external time boundary with `Final Result: Fail`; the remaining `Admitted.` lines are intentionally left visible rather than hidden.

## 2026-04-22 retry proof round 1

Before editing this retry, I recompiled the current generated Coq chain through `string_collapse_spaces_proof_manual.v` using the load path from `experiences/general/COMPILE.md`; it compiled because the four hard witnesses are still `Admitted.`:

```coq
Lemma proof_of_string_collapse_spaces_entail_wit_2_1 : string_collapse_spaces_entail_wit_2_1.
Proof. Admitted.
Lemma proof_of_string_collapse_spaces_entail_wit_2_2 : string_collapse_spaces_entail_wit_2_2.
Proof. Admitted.
Lemma proof_of_string_collapse_spaces_entail_wit_2_3 : string_collapse_spaces_entail_wit_2_3.
Proof. Admitted.
Lemma proof_of_string_collapse_spaces_return_wit_1 : string_collapse_spaces_return_wit_1.
Proof. Admitted.
```

The first concrete Coq state inspected was `string_collapse_spaces_entail_wit_2_2`. After `unfold`, `pre_process`, and `Intros`, the key hypotheses are:

```coq
H : in_space <> 0
H0 : Znth i (l ++ [0]) 0 = 32
H7 : 0 <= in_space
H8 : in_space <= 1
H9 : l = lin_2 ++ lrest_2
H10 : Zlength lin_2 = i
H12 : j = Zlength (string_collapse_spaces_spec lin_2)
H14 : in_space = 1 -> 0 < i /\ Znth (i - 1) l 0 = 32
```

The target must re-establish the invariant after reading another space while already in a space run. The necessary witness shape is `lin = lin_2 ++ [32]` and `lrest = xs` after destructing `lrest_2` as `32 :: xs`; `dout` remains `dout_2` because this branch does not write output. The proof needs a local helper that turns the invariant's previous-character fact `Znth (Zlength lin_2 - 1) lin_2 0 = 32` into `string_collapse_spaces_spec (lin_2 ++ [32]) = string_collapse_spaces_spec lin_2`.

For the write branches `entail_wit_2_1` and `entail_wit_2_3`, the inspected goal shows the output heap after the C store:

```coq
CharArray.full out_pre (n + 1)
  (replace_Znth j 32 (string_collapse_spaces_spec lin_2 ++ dout_2))
```

or the same shape with the non-space current character. The planned proof witnesses are `lin = lin_2 ++ [current]`, `lrest = xs`, and `dout = tl dout_2`; this requires a helper lemma normalizing `replace_Znth (Zlength prefix) v (prefix ++ suffix)` to `prefix ++ [v] ++ tl suffix` when the suffix is non-empty. The non-emptiness of the output suffix should come from `CharArray.full_length` on the output heap plus `j <= i < n`.

## 2026-04-22 retry proof round 1 result

This retry added and compiled these reusable local helper lemmas in `coq/generated/string_collapse_spaces_proof_manual.v`:

```coq
sccs_replace_Znth_at_app
sccs_last_Znth
sccs_spec_snoc_space_emit_by_Znth
sccs_spec_snoc_space_suppress_by_Znth
```

I attempted `proof_of_string_collapse_spaces_entail_wit_2_1` using the witness shape `lin = lin_2 ++ [32]`, `lrest = xs`, and `dout = ys` after destructing `lrest_2 = 32 :: xs` and `dout_2 = y :: ys`. The helper lemmas were enough to prove the branch-specific spec fact:

```coq
Hemit :
  string_collapse_spaces_spec (lin_2 ++ [32]) =
  string_collapse_spaces_spec lin_2 ++ [32]
```

The stable remaining `entailer!` cleanup goals were:

```coq
Zlength (lin_2 ++ [32]) = i + 1
lin_2 ++ 32 :: xs = (lin_2 ++ [32]) ++ xs
1 = 1 -> 0 < i + 1 /\ Znth (i + 1 - 1) (lin_2 ++ 32 :: xs) 0 = 32
Zlength (string_collapse_spaces_spec lin_2) + 1 =
  Zlength (string_collapse_spaces_spec (lin_2 ++ [32]))
```

The partial witness script was not left in place because it made `proof_manual.v` fail to compile. I restored the four generated `Admitted.` placeholders so the workspace remains in the same compiling fail state as before, but with the helper lemmas preserved for the next retry. The next proof attempt should assert the four facts above before `entailer!` rather than trying to solve them after `entailer!` has split the goal.

## 2026-04-22 retry proof round 2

This retry continues at `proof_of_string_collapse_spaces_entail_wit_2_1` in `coq/generated/string_collapse_spaces_proof_manual.v`; the file still has the four generated placeholders:

```coq
Proof. Admitted. (* entail_wit_2_1 *)
Proof. Admitted. (* entail_wit_2_2 *)
Proof. Admitted. (* entail_wit_2_3 *)
Proof. Admitted. (* return_wit_1 *)
```

The current target from `coq/generated/string_collapse_spaces_goal.v` lines 549-595 is the branch where `in_space = 0` and the current input byte is `32`. The key generated facts after `pre_process` are expected to be:

```coq
Hspace : Znth i (l ++ [0]) 0 = 32
Hsplit : l = lin_2 ++ lrest_2
Hlenlin : Zlength lin_2 = i
Hj : j = Zlength (string_collapse_spaces_spec lin_2)
Hout :
  CharArray.full out_pre (n + 1)
    (replace_Znth j 32 (string_collapse_spaces_spec lin_2 ++ dout_2))
```

The previous retry established the useful branch spec equality but let `entailer!` split the remaining pure goals too early:

```coq
string_collapse_spaces_spec (lin_2 ++ [32]) =
  string_collapse_spaces_spec lin_2 ++ [32]
```

This round will first assert the facts that should be available before `entailer!`:

```coq
i < n
lrest_2 = 32 :: xs
dout_2 = y :: ys
replace_Znth j 32 (string_collapse_spaces_spec lin_2 ++ dout_2) =
  string_collapse_spaces_spec (lin_2 ++ [32]) ++ ys
Zlength (lin_2 ++ [32]) = i + 1
l = (lin_2 ++ [32]) ++ xs
j + 1 = Zlength (string_collapse_spaces_spec (lin_2 ++ [32]))
```

The output suffix destruct is justified by `CharArray.full_length` on the output heap, `j = Zlength (string_collapse_spaces_spec lin_2)`, and `j <= i < n`, which should imply the suffix length is positive. The proof edit will keep the existing helper lemmas and only replace the body of `proof_of_string_collapse_spaces_entail_wit_2_1`.

The first compile of this edit did not reach the semantic proof state because `Local Open Scope sac` changed parsing of the Ltac semicolon/bracket form:

```text
File ".../string_collapse_spaces_proof_manual.v", line 232, characters 49-51:
Error: Syntax error: [ltac_expr] or [tactic_then_locality] expected after ';' (in [ltac_expr]).
```

The offending tactic was:

```coq
destruct (Z.eq_dec i n) as [Hi_eq | Hi_neq]; [| lia].
```

I will rewrite this split with ordinary bullets instead of the bracketed semicolon form so the proof can reach the actual arithmetic/list obligations.

After that syntax fix, compile reached the intended contradiction but `lia` could not finish:

```text
File ".../string_collapse_spaces_proof_manual.v", line 238, characters 6-9:
Error: Tactic failure: Cannot find witness.
```

`coqtop` showed that after assuming `i = n`, rewriting `Znth i (l ++ [0]) 0 = 32` with `app_Znth2` and `Zlength l = n` left the concrete hypothesis:

```coq
H0 : Znth (Zlength lin_2 - n) [0] 0 = 32
Hi_eq : Zlength lin_2 = n
```

The missing step is not arithmetic alone; the index must first be normalized to `0`, after which `simpl in H0` yields `0 = 32`. I will add `replace (Zlength lin_2 - n) with 0 in H0 by lia` before `simpl in H0`.

Compiling after the index normalization still failed at the same final `lia`. The context is now an impossible concrete equality produced by `simpl in H0`, so I will close that branch by inversion/discrimination on `H0` instead of asking `lia` to solve it under the current open scopes.

The next compile failed on the list destruct intro-pattern:

```text
File ".../string_collapse_spaces_proof_manual.v", line 241, characters 22-24:
Error: Syntax error: [equality_intropattern] or [or_and_intropattern_loc] expected after 'as' (in [as_or_and_ipat]).
```

The source was `destruct lrest_2 as [| cur xs]`. Under this generated proof file's notation stack, the bracket intro-pattern is parsed poorly. I will switch list destructs to `destruct ... eqn:...` and then rename the generated cons variables explicitly in the cons branch.

The next compile reached the output suffix length assertion and failed because the length fact from `prop_apply CharArray.full_length` is named `H20` and is expressed through `Z.of_nat (length ...)`, not through `Zlength` directly:

```text
File ".../string_collapse_spaces_proof_manual.v", line 263, characters 4-41:
Error: Found no subterm matching "Zlength (replace_Znth ...)" in H.
```

The fix is to first derive a local `Hout_len : Zlength (replace_Znth j 32 (...)) = n + 1` by rewriting `Zlength_correct` and using `H20`, then rewrite `sccs_replace_Znth_length` and `Zlength_app` in that local fact.

The next compile showed the direction of the `j` rewrite was wrong:

```text
File ".../string_collapse_spaces_proof_manual.v", line 272, characters 4-27:
Error: Found no subterm matching "j" in Hout_len.
```

After `Zlength_app`, the fact contains `Zlength (string_collapse_spaces_spec lin_2)`, while `H12` is `j = Zlength (...)`; the needed rewrite is `rewrite <- H12 in Hout_len`.

Compilation then reached the spec-snoc helper premise and hit another bracketed tactic parse issue:

```text
File ".../string_collapse_spaces_proof_manual.v", line 291, characters 17-19:
Error: Syntax error: ']' expected after [for_each_goal] (in [ltac_expr]).
```

The proof also needs one more explicit bridge: `sccs_spec_snoc_space_emit_by_Znth` wants the previous-character fact on `lin_2`, while the invariant provides it on `l`. I will rewrite the split with bullets and derive `Znth (i - 1) lin_2 0 <> 32` by applying `H13`, rewriting `l = lin_2 ++ 32 :: xs`, and using `app_Znth1`.

The branch spec fact now compiles, and the next failure is the append association in `Hreplace`:

```text
Unable to unify "(string_collapse_spaces_spec lin_2 ++ [32]) ++ ys" with
 "string_collapse_spaces_spec lin_2 ++ 32 :: tl (y :: ys)".
```

After `sccs_replace_Znth_at_app` and `Hemit`, the two sides differ only by associativity and the simplification of `tl (y :: ys)`. I will add `rewrite <- app_assoc` before `reflexivity` in the `Hreplace` assertion.

The proof then reached the final `entailer!` cleanup. The first remaining goal no longer contained `l`, so `rewrite Hsplit_next` failed:

```text
File ".../string_collapse_spaces_proof_manual.v", line 337, characters 4-23:
Error: Found no subterm matching "l" in the current goal.
```

This is the pure append-shape goal `lin_2 ++ 32 :: xs = (lin_2 ++ [32]) ++ xs`; it should be solved directly with `rewrite <- app_assoc`. I will also make the previous-character cleanup explicit by introducing the implication premise, rewriting `l` via `Hsplit_next`, and using `app_Znth2` at index `i = Zlength lin_2`.

`coqtop` inspection showed the actual five subgoals left after `entailer!; try lia` are, in order:

```coq
forall k_2, 0 <= k_2 < n -> Znth k_2 ((lin_2 ++ [32]) ++ xs) 0 <> 0
forall k_2, 0 <= k_2 < n -> Znth k_2 ((lin_2 ++ [32]) ++ xs) 0 <> 0
1 = 1 -> 0 < i + 1 /\ Znth (i + 1 - 1) ((lin_2 ++ [32]) ++ xs) 0 = 32
Zlength ((lin_2 ++ [32]) ++ xs) = n
Zlength ((lin_2 ++ [32]) ++ xs) = n
```

So the previous bullets were ordered for the wrong goals. The two forall goals should rewrite back through `Hsplit_next` and apply the preserved no-zero hypotheses `H15`/`H19`; the previous-character goal should index into `(lin_2 ++ [32])` with `app_Znth1`, then into the appended singleton with `app_Znth2`; and the two length goals should rewrite back through `Hsplit_next` and reuse `H11`/`H18`.

After this change, the compile chain through `coq/generated/string_collapse_spaces_proof_manual.v` succeeded for `proof_of_string_collapse_spaces_entail_wit_2_1`; the remaining admitted loop witnesses are now `entail_wit_2_2` and `entail_wit_2_3`.

For `entail_wit_2_2`, `goal.v` lines 597-643 show the repeated-space branch: `in_space <> 0`, current input byte is `32`, and no output write occurs. The proof plan is to derive `in_space = 1` from `0 <= in_space <= 1`, split `lrest_2 = 32 :: xs`, use the invariant fact `H14 : in_space = 1 -> 0 < i /\ Znth (i - 1) l 0 = 32`, bridge that previous-character fact back to `lin_2`, and apply `sccs_spec_snoc_space_suppress_by_Znth` to prove:

```coq
string_collapse_spaces_spec (lin_2 ++ [32]) =
  string_collapse_spaces_spec lin_2
```

The witnesses should be `dout_2`, `lin_2 ++ [32]`, and `xs`.

For `entail_wit_2_3`, `goal.v` lines 645-690 show the nonzero non-space branch. The proof should mirror `entail_wit_2_1`, but with current head `cur` from `lrest_2 = cur :: xs`, branch fact `cur <> 32`, and helper `sccs_spec_snoc_nonspace`. The output suffix must again be non-empty via `CharArray.full_length`, and `replace_Znth` normalizes at `j = Zlength (string_collapse_spaces_spec lin_2)`.

The `entail_wit_2_2` implementation compiled successfully. I am now replacing `entail_wit_2_3`. The concrete proof bridge for this branch is:

```coq
Hread : Znth i (l ++ [0]) 0 = cur
Hnonspace : cur <> 32
Hspec :
  string_collapse_spaces_spec (lin_2 ++ [cur]) =
  string_collapse_spaces_spec lin_2 ++ [cur]
```

The generated heap writes `Znth i (l ++ [0]) 0`, so the proof will rewrite the store value with `Hread` before using `sccs_replace_Znth_at_app`.

The first compile of `entail_wit_2_3` failed in the `i < n` contradiction because I used the wrong hypothesis name:

```text
File ".../string_collapse_spaces_proof_manual.v", line 467, characters 6-36:
Error: Found no subterm matching "Znth ... (... ++ ...)" in H1.
```

`coqtop` shows the branch context names are:

```coq
H  : Znth i (l ++ [0]) 0 <> 32
H0 : Znth i (l ++ [0]) 0 <> 0
H10 : Zlength l = n
H19 : Z.of_nat (length (replace_Znth ...)) = n + 1
```

So the `i = n` contradiction must rewrite `H0`, not `H1`.

After this correction, `entail_wit_2_3` compiled successfully. The only remaining generated manual placeholder is now:

```coq
Lemma proof_of_string_collapse_spaces_return_wit_1 : string_collapse_spaces_return_wit_1.
Proof. Admitted.
```

For `return_wit_1`, `goal.v` lines 692-720 show the loop exited with:

```coq
Znth i (l ++ [0]) 0 = 0
l = lin ++ lrest
Zlength lin = i
Zlength l = n
j = Zlength (string_collapse_spaces_spec lin)
forall k, 0 <= k < n -> Znth k l 0 <> 0
CharArray.full out_pre (n + 1)
  (replace_Znth j 0 (string_collapse_spaces_spec lin ++ dout))
```

The proof plan is:

1. Prove `i = n`: if `i < n`, then `app_Znth1` turns the terminator read into `Znth i l 0 = 0`, contradicting the no-interior-zero hypothesis.
2. With `i = n`, use `l = lin ++ lrest`, `Zlength lin = n`, and `Zlength l = n` to destruct `lrest`; the cons case contradicts the length equations, and the nil case gives `l = lin`.
3. Use `CharArray.full_length` on the output heap and `j <= i = n` to prove `dout` is nonempty, destruct it as `y :: t`, and normalize:

```coq
replace_Znth j 0 (string_collapse_spaces_spec l ++ y :: t) =
  string_collapse_spaces_spec l ++ [0] ++ t
```

4. Existentially instantiate the postcondition suffix with `t` and prove `Zlength t = n - Zlength (string_collapse_spaces_spec l)` from the output length fact.

The first return proof compile reached the `lrest` cons contradiction but `lia` could not find the nonnegativity witness:

```text
File ".../string_collapse_spaces_proof_manual.v", line 613, characters 4-7:
Error: Tactic failure: Cannot find witness.
```

After destructing `lrest`, the tail of the cons branch is a generated variable, not the original `lrest` name. I will rename the generated head/tail explicitly and use `Zlength_nonneg` on the tail before `lia`.

The next compile reached the final suffix-length calculation. After `rewrite Zlength_cons in Hout_len`, there is no `Zlength nil` subterm left:

```text
File ".../string_collapse_spaces_proof_manual.v", line 664, characters 2-33:
Error: Found no subterm matching "Zlength []" in Hout_len.
```

The length fact is already in a form `j + Z.succ (Zlength t) = n + 1`; with `j = Zlength (string_collapse_spaces_spec lin)`, plain `lia` is sufficient. I will remove the unnecessary `rewrite Zlength_nil in Hout_len`.

After removing that extra rewrite, the full Coq chain compiled successfully:

```text
coqc original/string_collapse_spaces.v
coqc coq/generated/string_collapse_spaces_goal.v
coqc coq/generated/string_collapse_spaces_proof_auto.v
coqc coq/generated/string_collapse_spaces_proof_manual.v
coqc coq/generated/string_collapse_spaces_goal_check.v
```

`coq/generated/string_collapse_spaces_proof_manual.v` now has completed proofs for:

```coq
proof_of_string_collapse_spaces_entail_wit_1
proof_of_string_collapse_spaces_entail_wit_2_1
proof_of_string_collapse_spaces_entail_wit_2_2
proof_of_string_collapse_spaces_entail_wit_2_3
proof_of_string_collapse_spaces_return_wit_1
```

The only `Axiom` text found by `rg -n "Admitted\\.|Axiom"` in the manual proof file is the imported library module name `Axioms` in the existing `Require Import` line; there are no `Admitted.` placeholders and no new manual axioms.
