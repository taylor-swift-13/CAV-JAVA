# Verification Issues

## Issue 1: missing loop invariant for second-largest scan

- Phenomenon: the active annotated file initially had no `Inv` before `for (i = 2; i < n; ++i)`, so symbolic execution had no loop-head summary connecting `max1`, `max2`, and the processed array prefix to the postcondition's `top` and `second` witnesses.
- Location: `annotated/verify_20260422_081724_array_second_largest.c`, before the `for` loop.
- Fix action: added a prefix invariant carrying `2 <= i <= n`, stable `a`/`n`, unchanged `IntArray::full(a, n, l)`, existential prefix indices `top` and `second`, `l[top] == max1`, `l[second] == max2`, `max1 > max2`, and the prefix bound `(forall k, 0 <= k && k < i && k != top => l[k] <= max2)`.
- Result: this gave the loop the right semantic shape, but the first `symexec` still failed to infer initialization witnesses automatically.

Key annotation:

```c
/*@ Inv Assert exists top second,
      2 <= i && i <= n &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l) == n &&
      (forall (p: Z) (q: Z),
        (0 <= p && p < q && q < n) => l[p] != l[q]) &&
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

## Issue 2: frontend could not synthesize initialization existential witnesses

- Phenomenon: the first `symexec` run failed at invariant initialization and left zero-byte generated Coq files.
- Trigger: plain `Inv exists top second` required the frontend to synthesize `top = 1, second = 0` in the swap branch and `top = 0, second = 1` in the non-swap branch.
- Evidence from `logs/qcp_run.log`:

```text
Target Proposition is:
EX second_135 top_136
...
exist_mapping:
136 -> NULL
135 -> NULL
symexec_status=1
```

- Fix action: changed the loop annotation to `Inv Assert exists top second`, which turns the invariant-entry existential into generated manual entailment obligations.
- Result: after removing failed intermediate assertion attempts, `symexec` succeeded and generated nonempty `array_second_largest_goal.v`, `array_second_largest_proof_auto.v`, `array_second_largest_proof_manual.v`, and `array_second_largest_goal_check.v`.

## Issue 3: disjunctive bridge assertion was rejected

- Phenomenon: an attempted pre-loop `which implies` bridge with a top-level disjunction was rejected before VC generation.
- Triggering snippet:

```c
((max1 == l[0] && max2 == l[1]) ||
 (max1 == l[1] && max2 == l[0]))
```

- Error:

```text
fatal error: Multiple cases inside pre- or post-condition
```

- Fix action: removed the disjunctive bridge and did not use a multi-case assertion in the final annotation.
- Result: the final solution relies on `Inv Assert` plus manual Coq witnesses rather than a frontend disjunction.

## Issue 4: branch-local assertion lost block-local `t` permission

- Phenomenon: adding an `Assert exists top second` inside the swap branch failed while leaving the block that declares `int t`.
- Error:

```text
fatal error: Error: Fail to Remove Memory Permission of t:112
```

- Location: assertion inside:

```c
if (max2 > max1) {
    int t = max1;
    max1 = max2;
    max2 = t;
    /* failed assertion was here */
}
```

- Fix action: removed the inside-block assertion. Assertions that do not preserve local stack variables should not be inserted before block-local cleanup.
- Result: this failure disappeared; the final annotation has no assertion inside the `t` block.

## Issue 5: pre-loop post-block assertion lost uninitialized `i` permission

- Phenomenon: a standalone post-`if` assertion before `for (i = 2; ...)` failed because it did not preserve the local permission for uninitialized `i`.
- Error:

```text
fatal error: cannot find the program variable i(99) in assertion
```

- Fix action: removed the standalone assertion and kept the proof obligation attached to the loop annotation with `Inv Assert`.
- Result: `symexec` could proceed and generate Coq files.

## Issue 6: invariant initially omitted pairwise distinctness needed by proof

- Phenomenon: after the first successful `symexec`, the manual proof for `entail_wit_2_2` could not prove `max1 > Znth i l 0`.
- Trigger: in the `else if (a[i] > max2)` branch, C gives `Znth i l 0 <= max1`, but strictness requires knowing `Znth i l 0` is distinct from the old top value `max1`.
- Missing context before the fix:

```coq
H  : Znth i l 0 > max2
H0 : Znth i l 0 <= max1
H9 : Znth top_2 l 0 = max1
```

- Fix action: strengthened the loop invariant to preserve:

```c
Zlength(l) == n &&
(forall (p: Z) (q: Z),
  (0 <= p && p < q && q < n) => l[p] != l[q]) &&
```

- Result: after rerunning `symexec`, the generated proof context contained the distinctness hypothesis, and the manual proof used it to prove strictness.

## Issue 7: manual proof hypothesis names and subgoal order needed inspection

- Phenomenon: the first manual proof attempt failed because it destructed an unnamed assertion as `H`, colliding with a generated hypothesis; the next attempt guessed the pairwise-distinct hypothesis name incorrectly.
- Errors:

```text
Error: Expects a disjunctive pattern with 1 branch or a conjunctive pattern made of 0 patterns.
Error: The expression "H2" of type "Zlength l = n_pre" cannot be applied to the term "0" : "Z"
```

- Fix action: used `coqtop` to inspect the exact proof states, named case assertions explicitly as `Hcase`, and used the actual/generated hypotheses or `match goal` patterns for the quantified invariant facts.
- Result: `array_second_largest_proof_manual.v` compiles with no `Admitted.` and no new `Axiom`.

## Issue 8: final compilation left Coq intermediate files

- Phenomenon: successful compilation produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `coq/generated/`.
- Fix action: ran `find .../coq -type f ! -name '*.v' -delete`.
- Result: follow-up `find .../coq -type f ! -name '*.v'` returned no files.
