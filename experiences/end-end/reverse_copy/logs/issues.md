## 2026-04-22T21:29:43+08:00 - Workspace fingerprint initially had empty semantic fields

- Phenomenon: `logs/workspace_fingerprint.json` started with `"semantic_description": ""` and `"keywords": {}`.
- Trigger: the verify workflow requires reading `doc/retrieval/INDEX.md` early and then filling these fields using only the controlled vocabulary.
- Location: `output/verify_20260422_212943_reverse_copy/logs/workspace_fingerprint.json`.
- Fix: filled a semantic description for the reverse-copy loop and used controlled keys/values including `algorithm_family: two_pointers`, `control_flow: for_loop`, `data_shape: [array, pointer]`, `semantic_intent: [preserve_input, in_place_update]`, `proof_pattern: [loop_invariant, range_bound, heap_reasoning]`, `numeric_properties: [nonnegative_input, int_range]`, and `edge_case_behavior: empty_loop_possible`.
- Result: the fingerprint is non-empty and later records `verification_status: [goal_check_passed, proof_check_passed, manual_witness_needed]`.

## 2026-04-22T21:31:48+08:00 - Active annotated copy had input include depth

- Phenomenon: the first local `symexec` attempt failed before VC generation:

```text
fatal error: No such file ../verification_stdlib.h in search path in annotated/verify_20260422_212943_reverse_copy.c:1:35
```

- Trigger: the active annotated file was copied from `input/reverse_copy.c` and still used:

```c
#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"
```

- Location: `annotated/verify_20260422_212943_reverse_copy.c`.
- Fix: changed only the active annotated copy to the include depth used by current top-level active annotated files:

```c
#include "../../verification_stdlib.h"
#include "../../verification_list.h"
#include "../../int_array_def.h"
```

- Result: the next `symexec` run reached `reverse_copy`, finished symbolic execution, and generated fresh `reverse_copy_goal.v`, `reverse_copy_proof_auto.v`, `reverse_copy_proof_manual.v`, and `reverse_copy_goal_check.v`.

## 2026-04-22T21:32:34+08:00 - Reverse-copy loop needed a prefix/suffix invariant

- Phenomenon: the initial active annotated C file had a bare loop:

```c
for (i = 0; i < n; ++i) {
    dst[i] = src[n - 1 - i];
}
```

- Trigger: the postcondition requires `dst` to contain `rev(ls)`, but without an invariant there is no loop-head relationship between the copied reverse prefix, the untouched destination suffix, and the unchanged source array.
- Location: `annotated/verify_20260422_212943_reverse_copy.c`.
- Fix: added this invariant before the loop:

```c
/*@ Inv
      0 <= i && i <= n@pre &&
      src == src@pre &&
      dst == dst@pre &&
      n == n@pre &&
      Zlength(ls) == n@pre &&
      Zlength(ld) == n@pre &&
      IntArray::full(src, n@pre, ls) *
      IntArray::full(dst, n@pre,
        app(rev(sublist(n@pre - i, n@pre, ls)), sublist(i, n@pre, ld)))
*/
```

- Result: with the include fix, `symexec` succeeded on the latest annotated file. The generated loop-preservation VC reduced to a pure list normalization around `replace_Znth`, `rev`, `app`, and `sublist`.

## 2026-04-22T21:34:00+08:00 - Manual proof needed a local list-update helper

- Phenomenon: fresh `coq/generated/reverse_copy_proof_manual.v` contained three `Admitted.` placeholders:

```coq
Lemma proof_of_reverse_copy_entail_wit_1 : reverse_copy_entail_wit_1.
Lemma proof_of_reverse_copy_entail_wit_2 : reverse_copy_entail_wit_2.
Lemma proof_of_reverse_copy_return_wit_1 : reverse_copy_return_wit_1.
```

- Trigger: `entail_wit_2` had to prove that writing `src[n - 1 - i]` at `dst[i]` transforms:

```coq
app (rev (sublist (n_pre - i) n_pre ls)) (sublist i n_pre ld)
```

into:

```coq
app (rev (sublist (n_pre - (i + 1)) n_pre ls)) (sublist (i + 1) n_pre ld)
```

- Location: `output/verify_20260422_212943_reverse_copy/coq/generated/reverse_copy_proof_manual.v`.
- Fix: added local helper lemmas `Zlength_rev_Z` and `reverse_copy_replace_Znth`, then used the helper in `proof_of_reverse_copy_entail_wit_2`. The helper splits the source suffix into a singleton plus the old suffix, reverses it with `rev_app_distr`, splits the destination suffix at `i`, unfolds `replace_Znth` at offset `0`, and reassociates append.
- Result: `reverse_copy_proof_manual.v` compiles and contains no `Admitted.`, no top-level `Axiom`, and no `Parameter`.

## 2026-04-22T21:35:00+08:00 - `sublist_split` side conditions needed explicit length conversion

- Phenomenon: a compile attempt failed in `reverse_copy_replace_Znth` with:

```text
Error: Tactic failure: Cannot find witness.
```

at:

```coq
rewrite (sublist_split i n (i + 1) ld) by lia.
```

- Trigger: the side condition needed the bridge from `Zlength ld = n` to the length form expected by the selected `sublist_split` lemma. Plain `lia` did not introduce that conversion fact.
- Fix: solved split side conditions with explicit conversion facts:

```coq
rewrite (sublist_split i n (i + 1) ld) by (pose proof (Zlength_correct ld); lia).
rewrite (sublist_split (n - 1 - i) n (n - i) ls) by (pose proof (Zlength_correct ls); lia).
```

- Result: compilation advanced past the split side conditions.

## 2026-04-22T21:36:00+08:00 - Source singleton split and append associativity needed explicit normalization

- Phenomenon: the next compile failed because `sublist_single` expected the upper bound syntactically as `start + 1`, but the current term was printed as:

```coq
sublist (n - 1 - i) (n - i) ls
```

After fixing that, Coq still saw:

```coq
rev old ++ replace_Znth 0 x (old_head :: suffix)
```

instead of:

```coq
(rev old ++ x :: nil) ++ suffix
```

- Fix: replaced the exact source sublist with a singleton using a separate `replace ... with ...` block proved by `sublist_single`, then unfolded `replace_Znth` at `0` and rewrote append associativity:

```coq
replace (sublist (n - 1 - i) (n - i) ls)
  with (cons (Znth (n - 1 - i) ls 0) nil).
...
unfold replace_Znth.
simpl.
rewrite <- app_assoc.
simpl.
```

- Result: the full compile replay succeeded through `reverse_copy_goal_check.v`.

## 2026-04-22T21:37:10+08:00 - Final compile and cleanup completed

- Phenomenon: verification is not complete until the generated Coq chain compiles and non-`.v` intermediates are removed.
- Compile replay from `QualifiedCProgramming/SeparationLogic` succeeded for:

```text
reverse_copy_goal.v
reverse_copy_proof_auto.v
reverse_copy_proof_manual.v
reverse_copy_goal_check.v
```

- Cleanup: deleted all non-`.v` files under `output/verify_20260422_212943_reverse_copy/coq`. `input/` had no non-`.c`/non-`.v` intermediates.
- Result: `goal_check.v` passed, the manual proof has no forbidden stubs, and the workspace `coq/` tree contains only `.v` files.
