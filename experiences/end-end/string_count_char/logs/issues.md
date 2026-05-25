# Verification Issues

## Missing loop invariant in active annotated C

- Phenomenon: the active annotated file initially matched `input/string_count_char.c` and had no `Inv` before the `while (1)` loop. The loop reads `s[i]`, breaks when the terminator `0` is found, increments `ret` when `s[i] == c`, and then increments `i`. Without an invariant, symbolic execution would not preserve the relation between `ret` and the processed string prefix.
- Triggering C snippet:

```c
int i = 0;
int ret = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == c) {
        ret++;
    }
    i++;
}
```

- Fix action: added a prefix-count invariant to `annotated/verify_20260423_002212_string_count_char.c`:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= ret && ret <= i &&
      s == s@pre &&
      c == c@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      Zlength(l) == n &&
      ret == string_count_char_spec(l1, c) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Why this fixes the issue: `l1` is the processed prefix, `l2` is the unprocessed suffix, and `ret == string_count_char_spec(l1, c)` is exactly the loop accumulator meaning. The bound `0 <= ret && ret <= i` gives a local integer-safety path for `ret++`, because the branch that increments `ret` also has `i < n` and the contract has `n < INT_MAX`.
- Result: after adding the invariant and the loop-exit assertion, `symexec` succeeded and generated fresh `string_count_char_goal.v`, `string_count_char_proof_auto.v`, `string_count_char_proof_manual.v`, and `string_count_char_goal_check.v`.

## Loop-exit assertion needed to expose `i == n`

- Phenomenon: on the terminating branch, the C fact is `Znth i (l ++ [0]) 0 = 0`; the postcondition needs `ret == string_count_char_spec(l, c)`. The invariant only gives `ret == string_count_char_spec(l1, c)` for the processed prefix. The proof must know the terminator position is exactly `n`, not an earlier index.
- Fix action: added a loop-exit assertion immediately after the loop:

```c
/*@ Assert exists l1 l2,
      i == n &&
      0 <= ret && ret <= n &&
      s == s@pre &&
      c == c@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == n &&
      Zlength(l) == n &&
      ret == string_count_char_spec(l, c@pre) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

- Why this fixes the issue: the precondition states every `l[k]` for `0 <= k < n` is nonzero, while the array is `l ++ [0]`. Therefore a read of `0` at the loop head can only occur at index `n`. Once `i == n`, the processed prefix has length `n`, so it is the full list.
- Result: the generated exit witness `string_count_char_entail_wit_3` became a pure list/heap entailment and was completed in `proof_manual.v`.

## Manual witnesses required prefix-count list lemmas

- Phenomenon: after successful `symexec`, `coq/generated/string_count_char_proof_manual.v` contained four manual stubs:

```coq
Lemma proof_of_string_count_char_entail_wit_1 : string_count_char_entail_wit_1.
Lemma proof_of_string_count_char_entail_wit_2_1 : string_count_char_entail_wit_2_1.
Lemma proof_of_string_count_char_entail_wit_2_2 : string_count_char_entail_wit_2_2.
Lemma proof_of_string_count_char_entail_wit_3 : string_count_char_entail_wit_3.
```

- Localization: the hard witnesses are preservation after matching/nonmatching characters and the exit bridge. They require proving that extending `l1` by the current character updates `string_count_char_spec` consistently with the C branch.
- Fix action: added a local helper lemma and concrete proofs:

```coq
Lemma string_count_char_spec_app_single :
  forall (l : list Z) (x c : Z),
    string_count_char_spec (l ++ x :: nil) c =
    string_count_char_spec l c + (if Z.eq_dec x c then 1 else 0).
```

The preservation proofs destruct the current suffix, choose `l1_2 ++ [x]` as the next prefix, prove the append reassociation and prefix length before `entailer!`, and then use the helper lemma plus the branch fact `x = c_pre` or `x <> c_pre`.
- Result: `string_count_char_proof_manual.v` contains no `Admitted.` and no added `Axiom`; full compile replay passed through `string_count_char_goal_check.v`.

## Proof iteration subgoal-order failures

- Phenomenon: early manual scripts failed because they relied on the order of pure subgoals emitted by `entailer!`. Representative compile errors were:

```text
Error: Found no subterm matching "Zlength (?M13738 ++ ?M13739 :: nil)"
Error: Tactic failure: Cannot find witness.
Error: Found no subterm matching "(?M13739 ++ ?M13740) ++ ?M13741"
```

- Triggering proof shape:

```coq
Exists (l1_2 ++ x :: nil).
Exists xs.
entailer!.
+ rewrite Zlength_app_cons.
  lia.
+ ...
```

- Fix action: moved the required pure facts into named assertions before existential selection:

```coq
Happ : l1_2 ++ x :: xs = (l1_2 ++ x :: nil) ++ xs
Hlen_prefix : Zlength (l1_2 ++ x :: nil) = i + 1
Hspec_next : ret + 1 = string_count_char_spec (l1_2 ++ x :: nil) c_pre
```

For the exit witness, proved `Hl1_eq_l : l1_2 = l` and `Hspec_full : ret = string_count_char_spec l c_pre` before choosing `l` and `nil`.
- Result: the proof no longer depends on generated pure-goal ordering and compiled successfully.

## Cleanup after successful compile

- Phenomenon: successful `coqc` produced `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files under `output/verify_20260423_002212_string_count_char/coq/generated/`. A Coq auxiliary file also existed under `input/`.
- Fix action: removed all non-`.v` files under the workspace `coq/` directory and removed non-`.c`/non-`.v` files under root `input/`.
- Result: both cleanup checks returned empty output:

```text
find output/verify_20260423_002212_string_count_char/coq -type f ! -name '*.v'
find input -maxdepth 1 -type f ! -name '*.c' ! -name '*.v'
```
