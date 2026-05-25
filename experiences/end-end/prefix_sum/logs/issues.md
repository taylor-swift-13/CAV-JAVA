# Issues

## 2026-04-22 21:09 CST - First `symexec` failed on active annotated include paths

- Phenomenon: the first symbolic execution attempt did not reach VC generation.
- Trigger: the active annotated copy inherited input-style includes:

```c
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"
```

- Location: active annotated file line 1 and `logs/qcp_run.log` from the first run.
- Error text:

```text
fatal error: No such file ../verification_stdlib.h in search path in annotated/verify_20260422_210632_prefix_sum.c:1:35
symexec_status=1
```

- Fix action: changed only the active annotated working copy to the include layout used by verified examples:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```

- Result: the next `symexec` reached the loop body, confirming this was a front-end include search-path issue rather than a contract, invariant, or proof failure.

## 2026-04-22 21:09 CST - In-body bridge assertion dropped local scalar state for `acc`

- Phenomenon: after fixing include paths, `symexec` reached `acc += a[i]` but failed to derive the memory-read precondition.
- Trigger: the bridge before the compound assignment exposed `a[i]` with `IntArray::missing_i` and `data_at`, but the target assertion did not preserve the local scalar store for `acc`. A compound assignment needs to read and write `acc` as well as read `a[i]`.
- Location: active annotated file line 73 at the time of failure; `logs/qcp_run.log`.
- Error text:

```text
fatal error: Cannot derive the precondition of Memory Read. in annotated/verify_20260422_210632_prefix_sum.c:73:8
symexec_status=1
```

- Failing annotation shape:

```c
/*@ exists l1 l2,
      ...
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, app(l1, l2))
    which implies
      IntArray::missing_i(a, i, 0, n@pre, la) *
      data_at(a + (i * sizeof(int)), int, la[i]) *
      IntArray::full(out, n@pre, app(l1, l2))
*/
acc += a[i];
```

- Fix action: removed the three in-body bridge assertions around `acc += a[i]` and `out[i] = acc`, while keeping the full loop invariant:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      out == out@pre &&
      n == n@pre &&
      acc == sum(sublist(0, i, la)) &&
      ...
      IntArray::full(a, n@pre, la) *
      IntArray::full(out, n@pre, app(l1, l2))
*/
for (i = 0; i < n; ++i) {
    acc += a[i];
    out[i] = acc;
}
```

- Result: rerunning `symexec` from a clean `coq/generated` directory succeeded:

```text
End of symbolic execution of function prefix_sum
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-22 21:12 CST - Manual proof needed a prefix-sum snoc helper

- Phenomenon: after successful `symexec`, `coq/generated/prefix_sum_proof_manual.v` contained four generated admissions:

```coq
Lemma proof_of_prefix_sum_safety_wit_3 : prefix_sum_safety_wit_3.
Lemma proof_of_prefix_sum_entail_wit_1 : prefix_sum_entail_wit_1.
Lemma proof_of_prefix_sum_entail_wit_2 : prefix_sum_entail_wit_2.
Lemma proof_of_prefix_sum_return_wit_1 : prefix_sum_return_wit_1.
```

- Trigger: the generated goals needed the pure list fact that extending a prefix by `la[i]` updates the prefix sum:

```coq
sum (sublist 0 (i + 1) la) =
  sum (sublist 0 i la) + Znth i la 0
```

- Fix action: added local helper `prefix_sum_sum_sublist_snoc` in `proof_manual.v`, then used it to prove the overflow safety witness and the loop-preservation witness. The output-array reconstruction followed the existing array-write proof pattern: prove `l2_2 = sublist i n_pre lo`, choose `l1_2 ++ [sum(sublist 0 (i + 1) la)]` and `sublist (i + 1) n_pre lo`, normalize `replace_Znth` across `app`, then split the prefix value fact on `k < i` or `k = i`.
- Result: the helper and witness scripts compiled after correcting hypothesis references described below.

## 2026-04-22 21:13 CST - Copied proof skeleton used wrong generated hypothesis numbers

- Phenomenon: the first manual proof compile failed in `prefix_sum_entail_wit_2` while proving the suffix list equality.
- Error text:

```text
Ht : 0 <= t < Zlength l2_2
The term "Ht" has type "0 <= t < Zlength l2_2"
while it is expected to have type "0 <= t < n_pre - Zlength l1_2".
```

- Cause: the proof skeleton was adapted from `array_scale`, but the generated hypothesis numbering in `prefix_sum_entail_wit_2` differs. Here `H5` is `Zlength l1_2 = i`, `H6` is `Zlength l2_2 = n_pre - i`, `H7` is the prefix value fact, and `H8` is the suffix value fact.
- Fix action: changed the suffix equality proof to rewrite `Ht` using `H6`, call `H8`, and use `H5`/`H7` for prefix length and value facts.
- Result: compilation advanced to `prefix_sum_return_wit_1`.

## 2026-04-22 21:13 CST - Return witness used suffix length fact instead of prefix value fact

- Phenomenon: after fixing `entail_wit_2`, compilation failed in the return witness per-index postcondition.
- Error text:

```text
H7 :
  forall k_2 : Z,
  0 <= k_2 < Zlength l1 ->
  Znth k_2 l1 0 = sum (sublist 0 (k_2 + 1) la)
H6 : Zlength l2 = n_pre - Zlength l1
...
Unable to unify "Zlength l2 = n_pre - Zlength l1" with
 "Znth i l1 0 = sum (sublist 0 (i + 1) la)".
```

- Cause: the return proof also reused `apply H6` from a nearby example, but in this generated goal `H6` is the suffix length fact and `H7` is the completed-prefix value fact.
- Fix action: changed the return proof's per-index branch from `apply H6` to `apply H7`.
- Result: the full compile template passed:

```text
compiled prefix_sum_goal.v
compiled prefix_sum_proof_auto.v
compiled prefix_sum_proof_manual.v
compiled prefix_sum_goal_check.v
compile_end=2026-04-22T21:13:56+08:00
```

## 2026-04-22 21:14 CST - Final cleanup and verification checks

- Phenomenon: successful Coq compilation leaves `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` intermediates under `coq/generated`.
- Fix action: deleted non-`.v` files under `coq/` and, if present, non-`.v`/non-`.c` files under workspace-local `input/`.
- Result: only the four generated `.v` files remain under `coq/generated`; `proof_manual.v` contains no `Admitted.` and no top-level `Axiom`.
