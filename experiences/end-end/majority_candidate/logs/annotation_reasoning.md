# Annotation reasoning

## Initial loop invariant for `majority_candidate`

Program point: the only loop is `for (i = 1; i < n; ++i)` after initialization:

```c
int i;
int candidate = a[0];
int count = 1;

for (i = 1; i < n; ++i) {
    ...
}
```

The postcondition needs `__return == majority_candidate_spec(l)` and the input array unchanged.  The C loop is the same transition system as the Coq function `majority_candidate_acc`, but `input/majority_candidate.v` only exposes the final candidate function, not a pair-valued state function returning both candidate and count.  Therefore the invariant should not require a new count-state Coq helper.

Instead, at the loop test point, `i` is the next unprocessed index and the scalar state `(candidate, count)` is the accumulator state after processing `sublist(0, i, l)`.  This can be expressed using the existing Coq function by saying that if we continue the Coq accumulator from the current scalar state over the still-unprocessed suffix `sublist(i, n, l)`, we get the full-list specification:

```c
/*@ Inv
      1 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      0 <= count && count <= i &&
      majority_candidate_acc(candidate, count, sublist(i, n, l)) == majority_candidate_spec(l) &&
      IntArray::full(a, n, l)
*/
for (i = 1; i < n; ++i) { ... }
```

Initialization: before the first loop test, `i == 1`, `candidate == a[0]`, and `count == 1`.  Since `l` is nonempty (`1 <= n` and `Zlength(l) == n`), `majority_candidate_spec(l)` unfolds to `majority_candidate_acc(l[0], 1, tail l)`, which corresponds to `majority_candidate_acc(candidate, count, sublist(1, n, l))`.  The numeric bound `0 <= count && count <= i` holds because both are 1.

Preservation: each loop branch consumes exactly `a[i]`, which is the head of `sublist(i, n, l)` when `i < n`.  If `count == 0`, the Coq definition chooses the new accumulator `(a[i], 1)`.  If `count != 0 && a[i] == candidate`, it chooses `(candidate, count + 1)`.  Otherwise it chooses `(candidate, count - 1)`.  These are exactly the three C branches, and after the `for` increment the suffix becomes `sublist(i + 1, n, l)`.  The bound `0 <= count && count <= i` is strong enough to prove decrement nonnegativity and increment safety under `i < n` and `n <= INT_MAX`.

Exit usability: when the loop exits, `i == n`.  The invariant then gives `majority_candidate_acc(candidate, count, sublist(n, n, l)) == majority_candidate_spec(l)`, and the suffix is empty, so this reduces to `candidate == majority_candidate_spec(l)`.  I will add a loop-exit assertion immediately after the loop to make the return witness consume this fact at the right control point:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      candidate == majority_candidate_spec(l) &&
      IntArray::full(a, n, l)
*/
return candidate;
```

This assertion is deliberately small: it fixes the loop exit index, parameter preservation, the return value relation, and the array ownership needed by the postcondition.  It does not try to carry the now-irrelevant `count` fact into function exit.

## Frontend declaration fix for `majority_candidate_acc`

First `symexec` command:

```sh
QualifiedCProgramming/linux-binary/symexec --input-file=annotated/verify_20260422_190218_majority_candidate.c --goal-file=... --proof-auto-file=... --proof-manual-file=... --goal-check-file=... --coq-logic-path=SimpleC.EE.CAV.verify_20260422_190218_majority_candidate -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE --no-exec-info
```

It failed before VC generation with:

```text
fatal error: Use of undeclared identifier `majority_candidate_acc' in .../annotated/verify_20260422_190218_majority_candidate.c:32:4
```

The input `.v` defines `majority_candidate_acc`, and the annotated C already has `Import Coq Require Import majority_candidate`, but the annotation frontend also requires every Coq symbol used inside C annotations to appear in an `Extern Coq` declaration.  The current declaration only exposes `majority_candidate_spec`:

```c
/*@ Extern Coq (majority_candidate_spec : list Z -> Z) */
```

I will change only the active annotated copy to:

```c
/*@ Extern Coq (majority_candidate_acc : Z -> Z -> list Z -> Z)
               (majority_candidate_spec : list Z -> Z) */
```

This does not change the formal input contract or implementation.  It only lets the existing Coq helper from `input/majority_candidate.v` be referenced by the verify-stage loop invariant.

## Keep `count` in the loop-exit assertion

After adding the `Extern Coq` declaration, `symexec` reached the loop-exit assertion but failed at the assertion line with:

```text
fatal error: Error: Fail to Remove Memory Permission of count:104 in .../annotated/verify_20260422_190218_majority_candidate.c:51:4
```

The assertion was:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      candidate == majority_candidate_spec(l) &&
      IntArray::full(a, n, l)
*/
```

This was too small for the frontend because it mentioned `i` and `candidate` but dropped the still-live local `count` before the function return cleaned up locals.  I will keep a harmless pure bound for `count` in the exit assertion:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      0 <= count && count <= n &&
      candidate == majority_candidate_spec(l) &&
      IntArray::full(a, n, l)
*/
```

The added fact follows from the loop invariant `0 <= count && count <= i` and exit fact `i == n`.  It preserves the local variable in the assertion state while still leaving the return witness focused on `candidate == majority_candidate_spec(l)` and the unchanged input array.
