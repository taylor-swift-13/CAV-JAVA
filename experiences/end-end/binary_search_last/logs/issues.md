## 2026-04-22 09:34 +0800 - Workspace fingerprint started empty

- Phenomenon: `logs/workspace_fingerprint.json` still had the initialized placeholders:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the verify workflow requires this file to be useful for retrieval early in the task, and the user explicitly required reading `doc/retrieval/INDEX.md` before filling it.
- Localization: `output/verify_20260422_093407_binary_search_last/logs/workspace_fingerprint.json`.
- Fix: after reading `doc/retrieval/INDEX.md`, I filled `semantic_description` with the upper-bound binary-search behavior and used only controlled vocabulary values, including `algorithm_family: search`, `control_flow: ["while_loop", "if"]`, `data_shape: ["array", "pointer"]`, and proof-pattern keywords for loop invariant/range/monotonicity/case split.
- Result: the fingerprint is non-empty and, after final verification, was extended with `verification_status: ["goal_check_passed", "proof_check_passed"]`.

## 2026-04-22 09:35 +0800 - Missing loop summary for upper-bound binary search

- Phenomenon: the active annotated C initially copied the input C exactly and had no `Inv` or mid-range `Assert` around the loop:

```c
while (left < right) {
    mid = left + (right - left) / 2;
    if (a[mid] <= target) {
        left = mid + 1;
    } else {
        right = mid;
    }
}
```

- Trigger: `binary_search_last` needs to preserve the search-window semantics across a `while (left < right)` loop. Without a loop invariant, later witnesses would not know which prefix is `<= target`, which suffix is `> target`, or that `a`, `n`, and `target` are unchanged from pre-state.
- Localization: `annotated/verify_20260422_093407_binary_search_last.c`, immediately before the `while` loop and immediately after the midpoint assignment.
- Fix: following the verified `examples/binary_search_first/annotated/binary_search_first.c` pattern, I added an invariant with:

```c
0 <= left && left <= right && right <= n &&
a == a@pre && n == n@pre && target == target@pre &&
(forall (i: Z), (0 <= i && i < left) => l[i] <= target) &&
(forall (i: Z), (right <= i && i < n) => target < l[i]) &&
IntArray::full(a, n, l)
```

and a midpoint assertion containing:

```c
0 <= mid && mid < n &&
left <= mid && mid < right
```

- Result: a fresh `symexec` run on the updated annotated file completed successfully and generated `binary_search_last_goal.v`, `binary_search_last_proof_auto.v`, `binary_search_last_proof_manual.v`, and `binary_search_last_goal_check.v`.

## 2026-04-22 09:36 +0800 - Manual proof obligations after symexec

- Phenomenon: `symexec` succeeded, but `coq/generated/binary_search_last_proof_manual.v` contained six admitted manual obligations:

```coq
proof_of_binary_search_last_safety_wit_2
proof_of_binary_search_last_entail_wit_1
proof_of_binary_search_last_entail_wit_2
proof_of_binary_search_last_entail_wit_3_1
proof_of_binary_search_last_entail_wit_3_2
proof_of_binary_search_last_return_wit_2
```

- Trigger: the generated VCs include quotient bounds for `mid`, branch preservation of the binary-search invariant, and the final `return -1` not-found proof.
- Localization: `output/verify_20260422_093407_binary_search_last/coq/generated/binary_search_last_proof_manual.v`.
- Fix: I reused the verified proof pattern from `examples/binary_search_first/coq/generated/binary_search_first_proof_manual.v`, adapted for upper-bound search. The proof adds `binary_search_last_quot2_bounds`, proves the midpoint range with `Z.quot_pos`/`Z.quot_lt`, uses sortedness to preserve the suffix fact when `right = mid`, uses sortedness to preserve the prefix fact when `left = mid + 1`, and proves the `-1` return branch by choosing assertion-level `Right`.
- Result: all manual obligations are closed with `Qed`; `rg -n "Admitted\\.|^Axiom\\b" binary_search_last_proof_manual.v` returns no matches.

## 2026-04-22 09:37 +0800 - Tactic-pattern syntax error during compile replay

- Phenomenon: the first full compile replay failed in `binary_search_last_proof_manual.v` before a proof-state failure:

```text
File ".../binary_search_last_proof_manual.v", line 141, characters 76-78:
Error: Syntax error: ',' or '|-' expected (in [match_context_rule]).
```

- Trigger: one `match goal` tactic in `proof_of_binary_search_last_return_wit_2` omitted the required `|- _` separator:

```coq
match goal with
| Hupper: forall q, left <= q /\ q < n_pre -> target_pre < Znth q l 0 =>
    specialize (Hupper j ltac:(lia))
end.
```

- Localization: `output/verify_20260422_093407_binary_search_last/coq/generated/binary_search_last_proof_manual.v`, inside the suffix case of `proof_of_binary_search_last_return_wit_2`.
- Fix: changed the tactic pattern to:

```coq
match goal with
| Hupper: forall q, left <= q /\ q < n_pre -> target_pre < Znth q l 0 |- _ =>
    specialize (Hupper j ltac:(lia))
end.
```

- Result: the next full compile replay succeeded for `binary_search_last_goal.v`, `binary_search_last_proof_auto.v`, `binary_search_last_proof_manual.v`, and `binary_search_last_goal_check.v`.

## 2026-04-22 09:38 +0800 - Final compile and cleanup requirements

- Phenomenon: successful `symexec` and manual proof editing are not enough for completion; the workflow requires `goal_check.v` to compile and non-`.v` Coq build artifacts to be removed.
- Trigger: `coqc` generated `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files in `coq/generated/`.
- Localization: `output/verify_20260422_093407_binary_search_last/coq/generated/`.
- Fix: ran the full compile template from `QualifiedCProgramming/SeparationLogic` with generated logical path `SimpleC.EE.CAV.verify_20260422_093407_binary_search_last`, then deleted all files under `coq/` that do not end in `.v`.
- Result: `logs/compile_full.log` ended with `compile_status: 0`; `find output/verify_20260422_093407_binary_search_last/coq -type f ! -name '*.v'` returns no files.
