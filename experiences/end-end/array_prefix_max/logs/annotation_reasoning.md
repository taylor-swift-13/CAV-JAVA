## Initial loop invariant for prefix maximum output

Program point: the only loop is `for (i = 1; i < n; ++i)` after the initialization

```c
cur = a[0];
out[0] = cur;
for (i = 1; i < n; ++i) {
    if (a[i] > cur) {
        cur = a[i];
    }
    out[i] = cur;
}
```

The postcondition requires an output list `lr` such that for every index `p`, `lr[p]` is equal to some input element `la[j]` from the prefix `0 <= j <= p`, and every input element `la[k]` in that same prefix satisfies `la[k] <= lr[p]`. Because the loop writes `out` one index at a time, the heap invariant should split the output array into a written prefix and the original unwritten suffix:

```c
IntArray::full(out, n@pre, app(l1, sublist(i, n@pre, lo)))
```

Here `i` is the next index to be processed at the loop guard. The prefix `l1` has length `i`, so indices `0 .. i-1` have already been written. The invariant must preserve the postcondition shape for every written prefix index:

```c
Zlength(l1) == i &&
(forall (p: Z),
  (0 <= p && p < i) =>
  (exists j, 0 <= j && j <= p && l1[p] == la[j]) &&
  (forall (k: Z), (0 <= k && k <= p) => la[k] <= l1[p]))
```

The scalar `cur` is the prefix maximum for the already processed prefix `0 .. i-1`, which is exactly the value to write after extending the processed prefix with index `i`. The invariant therefore also records:

```c
(exists j, 0 <= j && j < i && cur == la[j]) &&
(forall (k: Z), (0 <= k && k < i) => la[k] <= cur)
```

Initialization holds after `out[0] = a[0]` with `i == 1`: choose `l1 = [la[0]]`; `cur == la[0]`; the existential witness for prefix index `0` is `j = 0`; and the domination fact only needs `k = 0`. The boundary `n > 0` is available because the `n == 0` branch has returned.

Preservation holds by case-splitting the conditional. If `a[i] > cur`, then `cur` becomes `la[i]`, so witness `j = i` proves it is an input element from the extended prefix, and the old domination plus the branch condition proves every old element is below the new `cur`. If `a[i] <= cur`, then the old witness for `cur` remains valid and the branch condition proves `la[i] <= cur`; hence the old `cur` is still a maximum of prefix `0 .. i`. Immediately before `out[i] = cur`, an `Assert` records this extended-prefix fact while the heap is still split at `i`.

At loop exit, the invariant gives `i == n@pre` together with the full output heap `app(l1, sublist(n@pre, n@pre, lo))`; this should reduce to a full output list with length `n@pre` and the required per-index prefix maximum relation. The invariant also records `a == a@pre`, `out == out@pre`, and `n == n@pre` so the return witness can match the `@pre` postcondition.

## Revision after first `symexec`: avoid existential prefix reconstruction at initialization

First `symexec` command:

```text
QualifiedCProgramming/linux-binary/symexec --input-file=annotated/verify_20260422_063947_array_prefix_max.c --goal-file=... --proof-auto-file=... --proof-manual-file=... --coq-logic-path=SimpleC.EE.CAV.verify_20260422_063947_array_prefix_max -slp QualifiedCProgramming/QCP_examples/ SimpleC.EE --no-exec-info
```

It failed at the invariant initialization for the loop head:

```text
Partial Solve Invariant Error ... verify_20260422_063947_array_prefix_max.c:54:4
Target Proposition includes:
replace_Znth(0, la[0], lo) == app(l1_134, sublist(1, Zlength(la), lo))
0 <= j_133; j_133 < 1; la[0] == la[j_133]
```

The failure is not that the desired invariant is semantically wrong. The problem is that the symbolic executor tried to infer both the initial prefix list `l1` and the witness index `j` automatically, and chose an unusable witness for `j` (`n@pre`) while leaving `l1` unresolved. This makes initialization fail before Coq proof generation.

To reduce front-end existential inference, I will change the heap part of the invariant from the split shape

```c
IntArray::full(out, n@pre, app(l1, sublist(i, n@pre, lo)))
```

to a whole-array ghost list:

```c
exists lr,
  Zlength(lr) == n@pre &&
  (forall p, 0 <= p && p < i => prefix-max property for lr[p]) &&
  (forall p, i <= p && p < n@pre => lr[p] == lo[p]) &&
  IntArray::full(out, n@pre, lr)
```

This matches the style used by simple array-update examples: the current concrete heap list can be `replace_Znth(0, la[0], lo)` at initialization, and later each write produces a new `lr'`. The invariant still carries exactly the postcondition information for the written prefix, while the unwritten suffix equality gives the value needed to open `out[i]` before assignment. The assertion after the conditional remains, but it now carries `lr` instead of `l1`; it records that `cur` is a maximum of the extended prefix `0 .. i`, which is the fact needed for the post-write `lr'` witness.

## Revision after second `symexec`: remove scalar provenance existential

The second `symexec` run used the whole-array `lr` shape, and the front-end correctly selected

```text
lr = replace_Znth(0, la[0], lo)
```

for the output heap. It still failed at loop-invariant initialization because the invariant also required a separate scalar provenance witness:

```c
(exists j, 0 <= j && j < i && cur == la[j])
```

The log again shows the solver choosing `j = n@pre`, which makes the target contain impossible facts such as `n@pre < 1` and `la[0] == la[n@pre]`.

This scalar existential is redundant for loop preservation. The written-output prefix already carries the postcondition provenance fact for every written index:

```c
(forall p, 0 <= p && p < i =>
  (exists j, 0 <= j && j <= p && lr[p] == la[j]) && ...)
```

The scalar `cur` only needs to dominate the processed prefix and match the last written output element. I will replace the scalar existential with:

```c
cur == lr[i - 1] &&
(forall k, 0 <= k && k < i => la[k] <= cur)
```

Initialization is then direct: after `out[0] = a[0]`, `lr[0]` is `la[0]`, so `cur == lr[0]` with `i == 1`. Preservation is also aligned with the code: after the conditional, either `cur == la[i]` when the branch updates it, or `cur` remains the old maximum `lr[i - 1]`; in both cases the following output write makes the new `lr'[i] == cur`, and the output-prefix provenance for `lr'[i]` can be proved in the generated Coq witness from the branch fact or from the previous `lr[i - 1]` provenance.

## Syntax fix for bridge assertion

The third `symexec` run failed in the parser:

```text
bison: syntax error, unexpected PT_WHICHIMPLIES, expecting PT_STARSLASH
```

The failing annotation used:

```c
/*@ Assert exists lr, ... which implies ... */
```

This is not accepted by the annotation grammar. Existing working array examples use `which implies` only in a plain bridge annotation:

```c
/*@ exists lr, ... which implies ... */
```

I will remove the `Assert` keyword from the pre-write bridge block. This preserves the intended control point and heap-opening transition but uses the grammar-supported form.

## Front-end case split fix: replace disjunction with implications

The next `symexec` run rejected the post-branch fact:

```text
Multiple cases inside pre- or post-condition ... verify_20260422_063947_array_prefix_max.c:59:8
```

The rejected annotation used an explicit disjunction:

```c
(cur == lr[i - 1] || cur == la[i])
```

Following the assertion experience for multi-branch facts, I will split this into two independent implications:

```c
(la[i] > lr[i - 1] => cur == la[i]) &&
(la[i] <= lr[i - 1] => cur == lr[i - 1])
```

This expresses the same branch-sensitive provenance without putting a disjunction directly inside the assertion. The first implication corresponds to the `if (a[i] > cur)` branch, using the invariant fact that the old `cur` equals `lr[i - 1]`. The second implication corresponds to the path where the assignment to `cur` is skipped.

## Remove pre-write `which implies` that dropped local `cur`

The next `symexec` run passed the multi-case parsing issue but failed at the concrete assignment:

```text
Error: cannot write null value to memory, maybe you try to read from an uninitialized program variable
Write to Address : out@pre + i * sizeof(int)
Current Assertion : exists lr_135 cur_134, ... IntArray.missing_i(out@pre, i, 0, n@pre, lr_135) * (*(out@pre + i * 4) == lo[i])
```

The pre-write `which implies` successfully opened the output cell but lost the local store/temporary needed to evaluate the right-hand side expression `cur`. I will change this block into a plain `Assert exists lr, ... IntArray::full(out, n@pre, lr)` without `which implies`. That keeps the branch facts and local-variable state at the control point; the assignment rule can open `out[i]` itself, and the post-write bridge can still reconstruct the full output array from the `missing_i + data_at(..., cur)` state.

## Revision after proof safety failure: preserve `n@pre <= INT_MAX`

The first `coqc` attempt on `proof_manual.v` failed in `proof_of_array_prefix_max_safety_wit_5`, whose target is the loop-step overflow condition:

```coq
i + 1 <= INT_MAX
```

Proof-state inspection after recovering the `i` stack-slot range showed:

```coq
H2 : 1 <= i
H3 : i < n_pre
H12 : Int.min_signed <= i <= Int.max_signed
```

There was no stack slot for `n` left in that witness, so the proof could not recover `n_pre <= INT_MAX`. The needed bridge is pure arithmetic:

```text
i < n@pre && n@pre <= INT_MAX => i + 1 <= INT_MAX
```

I will add `n@pre <= INT_MAX` to the loop invariant and preserve it through the pre-write assertion and post-write bridge target. This changes the VC shape, so the generated Coq files must be cleared and regenerated with `symexec`.

## Remove post-write `which implies` because it drops local stack stores

After adding `n@pre <= INT_MAX`, `symexec` succeeded, but manual proof inspection showed `array_prefix_max_entail_wit_3` was structurally impossible:

```coq
emp |-- &( "n") # Int |-> n_pre ** &( "cur") # Int |-> cur_2
```

The left side had only:

```coq
IntArray.full a_pre n_pre la ** IntArray.full out_pre n_pre lr'
```

while the next-loop invariant target required the local stack stores for `n` and `cur`. The cause is the post-write `which implies` block: like the earlier pre-write bridge, it reconstructed the heap but did not preserve local variables. This is an annotation-level problem, not a Coq tactic problem.

I will remove the post-write bridge block entirely. The assignment rule already produces a concrete `IntArray.full out_pre n_pre (replace_Znth i cur lr)` state while preserving stack locals. The loop invariant check should then generate proof obligations directly from that concrete state, with local stores available.

## Remove pre-write `Assert` because it also loses locals before loop preservation

After removing the post-write bridge, `symexec` still generated an impossible `entail_wit_3`: the left side contained only array heaps while the target next-loop invariant required stack stores for `n` and `cur`. That means the remaining pre-write `Assert exists lr, ... IntArray::full(...)` also reset the symbolic state in a way that loses locals before the loop preservation obligation.

I will remove the pre-write assertion entirely. The program state after the `if` already contains the branch path condition and old invariant facts. Letting the assignment execute directly should keep all local stores in the post-assignment state and avoid asking Coq to conjure stack permissions from `emp`.
