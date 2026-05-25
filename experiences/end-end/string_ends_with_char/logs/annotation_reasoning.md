## 2026-04-23 02:06 - Initial loop invariant for last-character scan

The active annotated file initially matched the input exactly and had no invariant before the `while (1)` loop:

```c
    while (1) {
        if (s[i + 1] == 0) {
            break;
        }
        i++;
    }
```

This loop cannot be symbolically executed without an invariant because the verifier must justify repeated reads of `s[i + 1]`, preservation of the `CharArray::full` resource, and the fact that the index found at loop exit is the last nonzero character. The earlier guard

```c
    if (s[0] == 0) {
        return 0;
    }
```

handles the empty string case. On the fallthrough path, the string is nonempty, so the loop starts with `i == 0`, `0 < n`, and `0 <= i < n`. The loop invariant should therefore describe `i` as the current last known nonzero index, while retaining the unchanged input pointer/value facts needed by the postcondition.

Planned annotation before the loop:

```c
    /*@ Inv Assert
          0 < n && 0 <= i && i < n &&
          s == s@pre &&
          c == c@pre &&
          Zlength(l) == n &&
          (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
          CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
```

Initialization: after the `s[0] == 0` branch is skipped, `i == 0`; because the concrete array element at index 0 is not the terminator and the logical array is `app(l, cons(0, nil))`, the empty case `n == 0` is impossible, so `0 < n` and `0 <= i < n` hold.

Preservation: at loop head, `0 <= i < n`, so `i + 1` is within the allocated `n + 1` character array. If `s[i + 1] == 0`, the loop breaks. Otherwise `s[i + 1] != 0`; since the only terminator in the logical representation is at index `n` and all indices `< n` are nonzero, the next state after `i++` satisfies `0 <= i + 1 < n`. The memory resource is read-only, so `CharArray::full(s, n + 1, app(l, cons(0, nil)))` is preserved.

Exit usability: after the break, we need to prove that `i` is exactly the last valid index. A small loop-exit assertion placed immediately after the loop records the pure consequence `i == n - 1` while preserving the same array resource:

```c
    /*@ Assert
          0 < n &&
          i == n - 1 &&
          s == s@pre &&
          c == c@pre &&
          Zlength(l) == n &&
          (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
          CharArray::full(s, n + 1, app(l, cons(0, nil)))
    */
```

This assertion is needed by the final `if (s[i] == c)` branches: in the true branch, `s[i] == c` plus `i == n - 1` establishes the second postcondition case; in the false branch, `s[i] != c` plus `i == n - 1` establishes the third postcondition case. It also keeps `s == s@pre` and `c == c@pre` available so generated return witnesses do not have to reconstruct unchanged parameter facts from local stores.

## 2026-04-23 02:11 - Strengthen invariant with `n < INT_MAX`

The first `proof_manual.v` compile attempt after successful `symexec` failed at `proof_of_string_ends_with_char_safety_wit_6`. The generated VC was:

```coq
Definition string_ends_with_char_safety_wit_6 :=
forall (c_pre s_pre n : Z) (l : list Z) (i : Z),
  [| 0 < n |] && [| 0 <= i |] && [| i < n |] &&
  [| Zlength l = n |] &&
  [| forall k, 0 <= k /\ k < n -> Znth k l 0 <> 0 |] &&
  ...
|--
  [| i + 1 <= INT_MAX |] && [| INT_MIN <= i + 1 |].
```

Running `coqtop` through `pre_process; entailer!; Show` left the subgoal:

```coq
H : 0 < n
H0 : 0 <= i
H1 : i < n
============================
i + 1 <= 2147483647
```

This is not provable from the current invariant because `n < INT_MAX` was present in the function precondition but was not preserved into the loop invariant. The correct fix is to strengthen the annotation rather than hard-code an impossible proof. I will add `n < INT_MAX` to both the loop invariant and the post-loop assertion:

```c
/*@ Inv Assert
      0 < n && n < INT_MAX && 0 <= i && i < n &&
      ...
*/

/*@ Assert
      0 < n && n < INT_MAX &&
      i == n - 1 &&
      ...
*/
```

Initialization follows directly from the function precondition. Preservation is immediate because `n` is a ghost input length and the loop does not modify it. Exit usability improves because the final read of `s[i]` also keeps the integer range facts needed for generated safety witnesses.
