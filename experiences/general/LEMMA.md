# Lemma Experience

OpenJML lemma support should be encoded as Java/JML artifacts that OpenJML can
check, not as unchecked axioms.

## Allowed Forms

- `pure` helper methods with full JML contracts and executable bodies.
- Small boolean predicates implemented as Java methods and specified with JML.
- Model methods only when their semantics are explicit and do not hide an
  unproved property.

## Rules

- A lemma helper must be verified by OpenJML together with the target file.
- Do not use `native`, empty bodies, or impossible preconditions to bypass proof.
- Do not move the core algorithm into a helper with a weaker specification.
- Keep helper methods deterministic and side-effect free.

## When To Use

- Reusable arithmetic facts.
- Reusable array segment predicates.
- Sortedness or prefix facts used in more than one assertion or invariant.

## Manual Notes

From `doc/openjml-tutorial/MethodsInSpecifications.html`:

- Methods called from specifications must be pure: they must not change the
  Java program state visible at the beginning of the call.
- Specification methods must also be deterministic. Do not use randomness,
  clocks, environment properties, I/O, or other changing external state.
- If a helper is used in `requires`, `ensures`, invariants, assertions, or
  quantifiers, give it a contract strong enough for callers; OpenJML reasons
  from the helper's specification, not from arbitrary inlining.

From `doc/openjml-tutorial/Lemmas.html`:

- Prefer a proved lemma over an assumption. A model lemma with a body `{}` is
  checked; the same declaration ending in `;` is assumed and is not acceptable
  for this workflow.
- Calling a lemma in JML instantiates its precondition and postcondition at
  specific values. The call is useful when a solver needs one connecting fact.
- A lemma body may be a sequence of checked `assert` statements that guide the
  solver through the proof.

From `doc/openjml-tutorial/ModelMethods.html`:

- Model methods are specification-only methods. They can be useful abstractions,
  but when used in specifications they should be `spec_pure` and have explicit
  contracts.
- Model methods with no implementation or insufficient contract behave like
  uninterpreted functions; use them only when the needed facts are supplied by
  invariants, preconditions, or postconditions.

From `doc/openjml-tutorial/ModelFields.html`:

- Model fields describe abstract state and are connected to concrete state with
  representation clauses in richer designs. They are usually unnecessary for
  small algorithmic examples; prefer direct executable helpers unless an
  abstraction is clearly needed.

From `doc/openjml-tutorial/Ghost.html`:

- Ghost variables and `set` statements are specification-only state. Use them
  sparingly to record proof-relevant values, and never to hide unproved facts.
