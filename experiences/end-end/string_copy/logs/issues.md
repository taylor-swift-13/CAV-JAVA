# Issues

## 2026-04-22 - Workspace fingerprint initialized from controlled vocabulary

- Phenomenon: `logs/workspace_fingerprint.json` still had the script placeholders:

```json
"semantic_description": "",
"keywords": {}
```

- Trigger: the verify workflow requires reading `doc/retrieval/INDEX.md` early and filling the fingerprint before continuing.
- Fix action: read the retrieval index, then updated the fingerprint with a non-empty description of the null-terminated string copy loop and controlled keywords only, including `algorithm_family: simulation`, `control_flow: while_loop`, `data_shape: [string, array, pointer]`, `proof_pattern: [loop_invariant, heap_reasoning]`, and final `verification_status: goal_check_passed`.
- Result: the fingerprint is no longer empty and uses only keys and values from the controlled vocabulary.

## 2026-04-22 - Missing loop invariant before string-copy scan

- Phenomenon: `input/string_copy.c` and the initial active annotated copy had no loop invariant for:

```c
while (1) {
    if (src[i] == 0) {
        break;
    }
    dst[i] = src[i];
    i++;
}
dst[i] = 0;
```

- Trigger: the loop reads `src[i]`, writes `dst[i]`, and must preserve enough heap and prefix information to prove the final destination equals `app(l, cons(0, nil))`.
- Fix action: added this invariant to `annotated/verify_20260422_235720_string_copy.c`:

```c
/*@ Inv exists l1 d1,
      0 <= i && i <= n &&
      src == src@pre &&
      dst == dst@pre &&
      Zlength(l1) == i &&
      Zlength(d1) == n + 1 - i &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      (forall (k: Z), (0 <= k && k < i) => l1[k] == l[k]) &&
      CharArray::full(src, n + 1, app(l, cons(0, nil))) *
      CharArray::full(dst, n + 1, app(l1, d1))
*/
```

- Result: after clearing stale generated files, `symexec` completed successfully against the active annotated file:

```text
End of symbolic execution of function string_copy
Successfully finished symbolic execution
symexec_status=0
```

## 2026-04-23 - Manual proof reuse needed generated-name hardening

- Phenomenon: the first adapted manual proof failed in `proof_of_string_copy_entail_wit_2`:

```text
Unable to unify "Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1"
with "Znth k (l1_2 ++ Znth i l 0 :: nil) 0 = Znth k l 0".
```

- Trigger: the archived proof shape matched the current VC semantically, but it depended on generated hypothesis names and the exact order of pure goals left by `entailer!`. In the current proof state, `H10` was the source length fact, while `H6` was the copied-prefix equality.
- Fix action: rewrote the preservation proof to prove the key facts before `entailer!`:

```coq
assert (Hlen_l1_new :
  Zlength (l1_2 ++ cons (Znth i l 0) nil) = i + 1).
assert (Hlen_l0 : Zlength l0 = n + 1 - (i + 1)).
assert (Hprefix_new :
  forall k : Z,
    0 <= k < i + 1 ->
    Znth k (l1_2 ++ cons (Znth i l 0) nil) 0 = Znth k l 0).
entailer!.
```

- Result: `proof_of_string_copy_entail_wit_2` no longer depends on fragile pure-goal bullet order and compiles.

## 2026-04-23 - Return proof stale hypothesis names

- Phenomenon: the next compile failed in `proof_of_string_copy_return_wit_1`:

```text
Illegal application: the expression "H10" of type
"Z.of_nat (Datatypes.length (l ++ 0 :: nil)) = n + 1"
cannot be applied to the term "i".
```

- Trigger: the archived script tried to use `H10` as the nonzero-prefix predicate to prove `i = n`, but the current generated context assigned `H10` to the length fact from `CharArray.full_length`.
- Fix action: selected the nonzero-prefix predicate by goal shape instead of by name:

```coq
match goal with
| Hnz : forall k : Z, 0 <= k < n -> Znth k l 0 <> 0 |- _ =>
    apply Hnz; lia
end
```

- A second stale-name failure occurred while proving `l1 = l`; the proof used the nonzero predicate `H5` where it needed the copied-prefix equality `H6`. Changing that line to `apply H6` fixed the extensional equality proof.
- Result: `string_copy_proof_manual.v` compiles with no `Admitted.` and no local `Axiom`.

## 2026-04-23 - Full compile and cleanup

- Phenomenon: after successful Coq compilation, generated `.vo`, `.glob`, `.vok`, `.vos`, and `.aux` files existed under `output/verify_20260422_235720_string_copy/coq/generated/`.
- Trigger: normal `coqc` output during the required full replay.
- Fix action: ran the full compile template from `QualifiedCProgramming/SeparationLogic` and then removed all non-`.v` files under the workspace `coq/` directory. Also checked `input/` for non-`.c`/non-`.v` intermediates.
- Result: the final compile log contains:

```text
compiled string_copy_goal.v
compiled string_copy_proof_auto.v
compiled string_copy_proof_manual.v
compiled string_copy_goal_check.v
```

After cleanup, `find output/verify_20260422_235720_string_copy/coq -type f ! -name '*.v'` and `find input -maxdepth 1 -type f ! -name '*.c' ! -name '*.v'` produce no output.
