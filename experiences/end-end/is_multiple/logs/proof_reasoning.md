# Proof Reasoning

## 2026-04-22 17:58:25 +0800 - Return witness proof plan after successful symexec

Current generated files are from the successful `symexec` run recorded in `logs/qcp_run.log`, which ended with `Successfully finished symbolic execution` and `symexec_status: 0` for `annotated/verify_20260422_175633_is_multiple.c`.

The generated manual proof file `output/verify_20260422_175633_is_multiple/coq/generated/is_multiple_proof_manual.v` contains exactly two unresolved manual obligations:

```coq
Lemma proof_of_is_multiple_return_wit_1 : is_multiple_return_wit_1.
Proof. Admitted.

Lemma proof_of_is_multiple_return_wit_2 : is_multiple_return_wit_2.
Proof. Admitted.
```

The first goal corresponds to the `return 1` branch. Its precondition in `is_multiple_goal.v` is:

```coq
[| ((a_pre % ( b_pre ) ) = 0) |] && [| (0 < b_pre) |] && emp
|-- ... || (EX q_2, [| 1 = 1 |] && [| a_pre = q_2 * b_pre |] && emp)
```

This is an assertion-level disjunction and existential, so the proof should use uppercase `Right` and `Exists`, not Coq's lowercase `right`/`exists`. The intended witness is `a_pre / b_pre`. From `0 < b_pre` we have `b_pre <> 0`; `Z.mod_divide` converts `a_pre % b_pre = 0` into an integer divisor relation, and commutativity of multiplication aligns Coq's divisor witness shape with the contract's `q * b_pre` shape.

The second goal corresponds to the `return 0` branch. Its precondition is:

```coq
[| ((a_pre % ( b_pre ) ) <> 0) |] && [| (0 < b_pre) |] && emp
|-- ([| 0 = 0 |] && [| forall q, a_pre <> q * b_pre |] && emp) || ...
```

The proof should use uppercase `Left`, introduce an arbitrary `q`, assume `a_pre = q * b_pre`, and contradict the branch fact by rewriting the modulo of a multiple to zero. I will first replace only these two `Admitted.` bodies in `proof_manual.v`, then compile the generated chain and inspect any remaining proof-state-specific failure.

## 2026-04-22 17:59:02 +0800 - First proof compile failure

The first full compile replay stopped in `output/verify_20260422_175633_is_multiple/coq/generated/is_multiple_proof_manual.v` at line 27:

```text
Error: The variable Hmod_to_div was not found in the current environment.
```

The failing proof fragment was:

```coq
destruct (Z.mod_divide a_pre b_pre) as [Hmod_to_div _].
assert (Hb_nonzero: b_pre <> 0) by lia.
pose proof (Hmod_to_div Hb_nonzero H) as [q Hq].
```

`Check Z.mod_divide` shows the lemma has shape:

```coq
forall a b : Z, b <> 0 -> a mod b = 0 <-> (b | a)
```

So the nonzero denominator proof must be supplied before destructing the iff. Next proof edit: assert `Hb_nonzero` first, destruct `(Z.mod_divide a_pre b_pre Hb_nonzero)`, and then apply the forward direction to the branch equality `H`.

## 2026-04-22 17:59:59 +0800 - C remainder notation is `Z.rem`, not `Z.modulo`

The second full compile replay stopped in the same manual file at line 27:

```text
The term "H" has type "a_pre % b_pre = 0" while it is expected to have type
 "a_pre mod b_pre = 0".
```

A `coqtop` check under the generated imports and scopes reported:

```text
Notation "x % y" := (Z.rem x y) (default interpretation)
```

Therefore the generated C `%` operator is Coq's truncating remainder `Z.rem`, not Euclidean modulo `Z.modulo`. Next proof edit: replace `Z.mod_divide` with `Z.rem_divide` and replace `Z.mod_mul` with `Z.rem_mul`. This matches the generated VC semantics without changing the C annotation or the contract.
