# Annotation Reasoning

## Initial loop invariant for `array_second_largest`

Current annotated file before this edit has no loop invariant:

```c
for (i = 2; i < n; ++i) {
    if (a[i] > max1) {
        max2 = max1;
        max1 = a[i];
    } else if (a[i] > max2) {
        max2 = a[i];
    }
}

return max2;
```

This is not enough for `symexec`, because the postcondition needs two indices `top` and `second` over the whole array such that `l[top]` is strictly larger than the returned value and every other element is at most the returned value. At the loop head, `i` is the next unprocessed index, so the stable state is about the processed prefix `0 <= k < i`.

The invariant to add before the `for` loop will state:

```c
/*@ Inv exists top second,
      2 <= i && i <= n &&
      n == n@pre &&
      a == a@pre &&
      0 <= top && top < i &&
      0 <= second && second < i &&
      top != second &&
      l[top] == max1 &&
      l[second] == max2 &&
      max1 > max2 &&
      (forall (k: Z), (0 <= k && k < i && k != top) => l[k] <= max2) &&
      IntArray::full(a, n, l)
*/
```

Initialization holds after the optional swap because the processed prefix is exactly indices `0` and `1`; the larger of `l[0]` and `l[1]` is `max1`, the smaller is `max2`, and pairwise distinctness from the function precondition gives the strict `max1 > max2`. Preservation matches the two update branches: if `a[i] > max1`, old `top` becomes the new `second` and index `i` becomes the new `top`; if `a[i] > max2` but not greater than `max1`, index `i` becomes the new `second`; otherwise both witnesses remain unchanged and the new element is covered by `l[i] <= max2`. Exiting the loop gives `i == n`, so the same existential witnesses satisfy the function postcondition after `return max2`. The invariant also keeps `n == n@pre`, `a == a@pre`, and `IntArray::full(a, n, l)` so the final memory postcondition and unchanged parameters are available to the generated witness.

## Initialization witness bridge after first `symexec` failure

The first `symexec` run failed at the loop invariant initialization and produced zero-byte generated Coq files. The relevant log is `logs/qcp_run.log` and the failure was:

```text
Target Proposition is:
EX second_135 top_136
PROP[
  0 <= top_136; top_136 < 2;
  0 <= second_135; second_135 < 2;
  top_136 != second_135;
  l[top_136] == l[1];
  l[second_135] == l[0];
  forall k, 0 <= k && k < 2 && k != top_136 -> l[k] <= l[0]]
...
exist_mapping:
136 -> NULL
135 -> NULL
symexec_status=1
```

This is the branch where the initial `if (max2 > max1)` swapped the two values, so the correct invariant witnesses are `top = 1` and `second = 0`. The tool did not infer them automatically. The next annotation edit will keep the semantic invariant unchanged but insert a `which implies` bridge immediately before the loop. The left side records the concrete two-element prefix facts available after initialization, and the right side is exactly the invariant initialization shape with existential `top` and `second`. This makes the missing existential witness explicit at the annotation boundary instead of asking the invariant checker to synthesize it silently.

That attempted bridge was rejected before VC generation:

```text
fatal error: Multiple cases inside pre- or post-condition
```

The rejected annotation used a top-level disjunction to describe the two possible initial orders:

```c
((max1 == l[0] && max2 == l[1]) ||
 (max1 == l[1] && max2 == l[0]))
```

This matches the warning in `experiences/general/ASSERTION.md`: multi-case assertions should not be packed into one pre/post condition. The next edit removes that disjunctive bridge and instead adds a smaller concrete assertion inside the swap branch, where the witness values are unambiguous (`top = 1`, `second = 0`), plus a post-`if` existential summary for the initialized two-element prefix.

The branch-local assertion also failed before VC generation:

```text
fatal error: Error: Fail to Remove Memory Permission of t:112
```

The assertion was inside the block that declares `int t`; by asserting only the high-level array/value state, it lost the local stack permission for `t`, so the frontend could not remove the block-local variable at `}`. The next edit removes the assertion from inside the `if` block and keeps the summary only after the block, where `t` is already out of scope.

The post-block assertion then failed at the `for` control point:

```text
fatal error: cannot find the program variable i(99) in assertion
```

The assertion was before the `for (i = 2; ...)` initializer and did not preserve the uninitialized local variable permission for `i`. Existing repository annotations use `Inv Assert exists ...` when the invariant entry itself should become an explicit entailment rather than a plain invariant synthesized entirely by the frontend. The next edit removes the standalone post-block assertion and changes the loop annotation from `Inv exists top second` to `Inv Assert exists top second`, keeping the same semantic invariant but letting the generated proof layer carry the difficult existential initialization witness.

## Strengthen invariant with distinctness after proof inspection

After `Inv Assert` allowed `symexec` to generate Coq files, proof inspection showed the invariant was still too weak for `entail_wit_2_2`, the branch for:

```c
} else if (a[i] > max2) {
    max2 = a[i];
}
```

The generated context included:

```coq
H  : Znth i l 0 > max2
H0 : Znth i l 0 <= max1
H9 : Znth top_2 l 0 = max1
```

but it did not include the original pairwise-distinct array property. The target requires:

```coq
max1 > Znth i l 0
```

This strict inequality follows from `Znth i l 0 <= max1`, `top_2 < i`, `Znth top_2 l 0 = max1`, and the function precondition that all elements at different indices are distinct. Because the invariant omitted both `Zlength(l) == n` and the pairwise-distinct fact, manual proof cannot derive the strict inequality. The next annotation edit adds these original pure facts to the loop invariant:

```c
Zlength(l) == n &&
(forall (p: Z) (q: Z),
  (0 <= p && p < q && q < n) => l[p] != l[q]) &&
```

This is a genuine invariant fix, not a proof tactic issue: the branch proof needs a semantic fact that was available before the loop and unchanged by the loop, but not preserved across the loop head.
