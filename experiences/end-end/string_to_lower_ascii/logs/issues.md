# Verification Issues

## 2026-04-23 loop invariant required for in-place string update

- Phenomenon: the active annotated C initially matched `input/string_to_lower_ascii.c` and had no `Inv` before the `while (1)` scan. Without an invariant, `symexec` would not have a loop-head assertion describing the transformed prefix, the still-original suffix, or the buffer ownership needed by the postcondition.
- Triggering code:

```c
int i = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] >= 65 && s[i] <= 90) {
        s[i] = s[i] + 32;
    }
    i++;
}
```

- Localization: `annotated/verify_20260423_044027_string_to_lower_ascii.c`, immediately before the `while (1)` loop.
- Fix action: added a prefix/suffix invariant with existential lists `l1` and `l2`:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      s == s@pre &&
      n == Zlength(l) &&
      Zlength(l1) == i &&
      Zlength(l2) == n + 1 - i &&
      (forall (t: Z), (0 <= t && t < i && 65 <= l[t] && l[t] <= 90) => l1[t] == l[t] + 32) &&
      (forall (t: Z), (0 <= t && t < i && (l[t] < 65 || 90 < l[t])) => l1[t] == l[t]) &&
      (forall (t: Z), (0 <= t && t < i) => l1[t] != 0) &&
      (forall (t: Z), (0 <= t && t < n - i) => l2[t] == l[i + t]) &&
      l2[n - i] == 0 &&
      CharArray::full(s, n + 1, app(l1, l2))
*/
```

- Result: after the parser repair below, `symexec` accepted this invariant and generated non-empty `goal`, `proof_auto`, `proof_manual`, and `goal_check` files.

## 2026-04-23 parser failure on `With` ghost variable `n@pre`

- Phenomenon: the first clean `symexec` run after adding the invariant failed before VC generation and left all generated Coq files at zero bytes.
- Triggering log from `logs/qcp_run.log`:

```text
symexec_start=2026-04-23 04:42:42 +0800
fatal error: Expected C expression in annotated/verify_20260423_044027_string_to_lower_ascii.c:22:1
Now parsing : n with type :2
symexec_status=1
```

- Localization: the active annotated postcondition used `n@pre` even though `n` is introduced by `With l n`, not by a C parameter or local declaration:

```c
Zlength(lr) == n@pre &&
(forall (i: Z), (0 <= i && i < n@pre) => ...) &&
(forall (k: Z), (0 <= k && k < n@pre) => lr[k] != 0) &&
CharArray::full(s, n@pre + 1, app(lr, cons(0, nil)))
```

- Fix action: changed only the active annotated verification copy, replacing those ghost-length occurrences with direct `n`. The formal input file under `input/` was not modified.
- Result: rerunning `symexec` on the cleaned generated directory completed successfully:

```text
symexec_start=2026-04-23 04:43:18 +0800
Symbolic Execution into function string_to_lower_ascii
End of symbolic execution of function string_to_lower_ascii
Successfully finished symbolic execution
symexec_elapsed=0
symexec_status=0
```

## 2026-04-23 manual proof obligation for invariant initialization

- Phenomenon: after successful `symexec`, `coq/generated/string_to_lower_ascii_proof_manual.v` contained one admitted manual obligation:

```coq
Lemma proof_of_string_to_lower_ascii_entail_wit_1 : string_to_lower_ascii_entail_wit_1.
Proof. Admitted.
```

- Localization: `string_to_lower_ascii_entail_wit_1` in `coq/generated/string_to_lower_ascii_goal.v` is the loop-invariant initialization entailment from the original heap `CharArray.full s_pre (n + 1) (app l (cons 0 nil))` to the invariant with existential `l1` and `l2`.
- Fix action: chose `l1 = nil` and `l2 = l ++ 0 :: nil`, then discharged the pure suffix and length goals using `app_Znth1`, `app_Znth2`, `Zlength_app`, and `lia`:

```coq
Proof.
  pre_process.
  Exists (l ++ 0 :: nil) (@nil Z).
  entailer!.
  - replace (n - 0) with (Zlength l) by lia.
    rewrite app_Znth2 by lia.
    replace (Zlength l - Zlength l) with 0 by lia.
    simpl. reflexivity.
  - intros t Ht.
    replace (0 + t) with t by lia.
    rewrite app_Znth1 by lia.
    reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.
```

- Result: `proof_manual.v` compiles and contains no `Admitted.` or newly added `Axiom`.

## 2026-04-23 final compile and cleanup

- Phenomenon: successful `symexec` and manual proof compilation are not sufficient; the verify workflow requires compiling `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v`, then deleting non-`.v` Coq intermediates under the current workspace.
- Fix action: compiled from `QualifiedCProgramming/SeparationLogic` with the documented base `-R` paths plus `-Q "$ORIG" ""` and `-R "$GEN" SimpleC.EE.CAV.verify_20260423_044027_string_to_lower_ascii`.
- Result from `logs/coq_compile.log`:

```text
goal: ok
proof_auto: ok
proof_manual: ok
goal_check: ok
```

- Cleanup result: removed generated `.vo`, `.vos`, `.vok`, `.glob`, and `.aux` files under `output/verify_20260423_044027_string_to_lower_ascii/coq/`. No non-`.c`/non-`.v` files existed under `input/`.
