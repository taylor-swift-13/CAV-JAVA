# Anti-Cheating Policy

Verification is useful only if success is not obtained by weakening the problem
or bypassing the verifier.

## Forbidden

- `assume`, especially `assume false`.
- `axiom`, `Admitted`, or similar unchecked proof claims.
- OpenJML suppression pragmas such as `skipesc` or broad `nowarn`.
- Weakening or deleting baseline `requires`, `ensures`, or `assignable` clauses.
- Adding over-strong preconditions that exclude normal inputs.
- Using `native`, reflection, or unchecked helper methods to hide behavior.
- Catching all failures or returning constants just to satisfy the postcondition.
- Marking a negative eval case as successful when OpenJML does not report
  the expected failure.

## Enforcement

`scripts/check_jml_cheating.py` scans Java files and, in verify mode, compares a
verified file against the original input contract. The verify wrapper must fail
if the scanner fails.

Scanner success is required before `Final Result: Success`.

## Manual Notes

From `doc/openjml-tutorial/AssumeStatement.html`:

- A JML `assume` tells the verifier to accept a predicate without proof. It can
  make invalid code verify, especially when the assumed predicate is false on a
  feasible path.
- `assume` may be useful only as a temporary proof-development sketch. This
  workflow forbids it in final contract, verify, and eval artifacts.
- Never replace a missing loop invariant, precondition, or lemma with `assume`.

From `doc/openjml-tutorial/Lemmas.html`:

- A lemma declaration ending with `;` is not proved by OpenJML. Treat it like an
  unchecked assumption unless there is an external proof, which this workflow
  does not accept.
- A proved lemma must have a body and must verify in the same OpenJML run as
  the target code.

From `doc/openjml-documentation/features.shtml.html`:

- OpenJML supports constructs such as `axiom`, `nowarn`, `spec_public`, `ghost`,
  `model`, and `pure`, but support does not make every construct acceptable for
  this automation workflow.
- Suppression features (`nowarn`, `skipesc`) and unchecked facts (`axiom`,
  unproved model methods, bodyless lemmas) bypass the evidence we need from
  OpenJML and are therefore forbidden here.

From `doc/openjml-tutorial/InitiallyConstraint.html`:

- Vacuous proofs can arise when inconsistent assumptions make a path
  impossible. Treat impossible preconditions and contradictory invariants as
  cheating even when OpenJML exits successfully.
