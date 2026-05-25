
## 2026-04-23 annotation iteration 1: add string scan invariant

Current annotated program has the original loop without an invariant:

```c
int i = 0;

while (1) {
    if (a[i] == 0) {
        break;
    }
    if (b[i] == 0) {
        break;
    }
    if (a[i] != b[i]) {
        return 0;
    }
    i++;
}
```

This cannot give `symexec` enough persistent loop state: after one or more iterations, the return branches must still know that both input arrays are the original arrays, that `i` is within both string lengths, and that all previously scanned characters are equal. The postcondition has two semantic cases. For return `1`, the proof needs both terminators at the same index and equality for every `k < na`; for the early mismatch return `0`, it needs an existential mismatch index. Those facts are not reconstructible from the bare loop counter after the loop body has abstracted previous iterations.

Planned invariant at the loop control point:

```c
/*@ Inv exists la1 la2 lb1 lb2,
      0 <= i && i <= na && i <= nb &&
      a == a@pre &&
      b == b@pre &&
      la == app(la1, la2) &&
      lb == app(lb1, lb2) &&
      Zlength(la1) == i &&
      Zlength(lb1) == i &&
      (forall (k: Z), (0 <= k && k < i) => la[k] == lb[k]) &&
      (forall (k: Z), (0 <= k && k < na) => la[k] != 0) &&
      (forall (k: Z), (0 <= k && k < nb) => lb[k] != 0) &&
      CharArray::full(a, na + 1, app(la, cons(0, nil))) *
      CharArray::full(b, nb + 1, app(lb, cons(0, nil)))
*/
```

Initialization: choose empty prefixes and the full original lists as suffixes. `i == 0`, `0 <= na`, and `0 <= nb` come from the precondition, so `i <= na` and `i <= nb` hold. The prefix equality quantifier is vacuous.

Preservation: on the path that continues past both terminator tests and the mismatch test, the program has `a[i] != 0`, `b[i] != 0`, and not `a[i] != b[i]`, so `la[i] == lb[i]`. Since `i <= na` and `i <= nb`, the false terminator tests force `i < na` and `i < nb`; after `i++`, both bounds become `i <= na` and `i <= nb`, and the prefix equality extends from `< old_i` to `< old_i + 1`.

Exit usability: if the loop exits because `a[i] == 0`, the invariant and the no-zero fact for `la[0..na)` imply `i == na`; similarly `b[i] == 0` implies `i == nb`. Therefore the final `if (a[i] == 0 && b[i] == 0)` return `1` branch gets `na == nb` and the invariant prefix equality covers all `k < na`. The final return `0` branch has exactly one terminator at `i`, so the lengths differ. The early mismatch return gets `i < na`, `i < nb`, and `la[i] != lb[i]`, which provides the existential mismatch required by the postcondition.

## 2026-04-23 annotation iteration 2: remove unnecessary existential prefix split

After the first successful `symexec`, `coq/generated/string_equal_proof_manual.v` contained six manual obligations. The hard obligation was `string_equal_entail_wit_2`, the loop preservation VC for extending the invariant after `i++`. Its target was forced by the invariant shape:

```coq
EX lb1 lb2 la1 la2,
  la = la1 ++ la2 /\
  lb = lb1 ++ lb2 /\
  Zlength la1 = i + 1 /\
  Zlength lb1 = i + 1 /\
  forall k, 0 <= k < i + 1 -> Znth k la 0 = Znth k lb 0
```

The C program never mutates either list and the postcondition only needs the direct prefix equality over the original `la` and `lb`; it does not need explicit prefix/suffix witnesses. The existential split made preservation require list decomposition proof work that is not semantically necessary for memory ownership, because the heap invariant already keeps both arrays as full arrays.

I am replacing the loop invariant with a smaller direct form:

```c
/*@ Inv
      0 <= i && i <= na && i <= nb &&
      a == a@pre &&
      b == b@pre &&
      (forall (k: Z), (0 <= k && k < i) => la[k] == lb[k]) &&
      (forall (k: Z), (0 <= k && k < na) => la[k] != 0) &&
      (forall (k: Z), (0 <= k && k < nb) => lb[k] != 0) &&
      CharArray::full(a, na + 1, app(la, cons(0, nil))) *
      CharArray::full(b, nb + 1, app(lb, cons(0, nil)))
*/
```

Initialization remains immediate because the prefix equality is vacuous at `i == 0`. Preservation still follows from the same branch facts: both terminator tests are false and `a[i] != b[i]` is false, so `i < na`, `i < nb`, and `la[i] == lb[i]`; the prefix equality extends to `i + 1`. Exit usability is unchanged: zero reads force `i == na` and/or `i == nb`, and the direct prefix equality is exactly the postcondition equality needed on the successful return branch. This edit should remove the unnecessary existential witness construction from `entail_wit_1` and `entail_wit_2`.
