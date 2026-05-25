# Annotation Reasoning

## Round 1: add local int-bound bridge and digit-count loop invariant

Current active file before this edit:

```c
/*@ Extern Coq (count_digits_spec : Z -> Z -> Prop) */
/*@ Import Coq Require Import count_digits */

int count_digits(int n)
...
{
    int cnt = 0;

    if (n == 0) {
        return 1;
    }

    while (n > 0) {
        cnt++;
        n = n / 10;
    }

    return cnt;
}
```

The unannotated loop loses the relation between the original input `n@pre`, the current quotient `n`, and the accumulated digit count `cnt`.  At loop entry after the `n == 0` branch, the remaining path has `0 < n@pre`, `cnt == 0`, and current `n == n@pre`.  Each loop iteration increments `cnt` and replaces `n` by the C quotient `n / 10`, so the invariant must state that `n@pre` lies in the interval represented by the current quotient after `cnt` decimal shifts:

```c
Zpower(10, cnt) * n <= n@pre &&
n@pre < Zpower(10, cnt) * (n + 1)
```

The lower final digit bound needed by the postcondition is not derivable at loop exit from the upper interval alone, so the invariant also carries:

```c
(cnt > 0 => Zpower(10, cnt - 1) <= n@pre)
```

The zero-iteration relation is:

```c
(cnt == 0 => n == n@pre)
```

This makes initialization immediate and lets the exit case prove `cnt > 0` for the positive-input path.

The older same-function workspace showed that `cnt++` generates a safety witness requiring `cnt + 1 <= INT_MAX`.  The formal input contract only says `0 <= n`, but the parameter is still held in an `Int` local cell near function entry.  Per `ASSERTION.md` section 8, I will add a local bridge:

```c
/*@ n <= INT_MAX by local */
```

before the branch, then carry `n@pre <= INT_MAX` through the invariant.  With the additional invariant fact `cnt + n <= n@pre`, the loop body guard `n > 0` gives `cnt + 1 <= n@pre <= INT_MAX`, which should discharge `cnt++` overflow without changing the formal input contract.

Planned annotated shape:

```c
/*@ Extern Coq (count_digits_spec : Z -> Z -> Prop) */
/*@ Extern Coq (Zpower : Z -> Z -> Z) */
/*@ Import Coq Require Import count_digits */
...
    int cnt = 0;

    /*@ n <= INT_MAX by local */

    if (n == 0) {
        return 1;
    }

    /*@ Inv
          0 < n@pre &&
          0 <= n &&
          0 <= cnt &&
          n@pre <= INT_MAX &&
          cnt + n <= n@pre &&
          (cnt == 0 => n == n@pre) &&
          (cnt > 0 => Zpower(10, cnt - 1) <= n@pre) &&
          Zpower(10, cnt) * n <= n@pre &&
          n@pre < Zpower(10, cnt) * (n + 1)
    */
    while (n > 0) { ... }
```

Initialization: after the nonzero branch, `0 < n@pre`, `cnt == 0`, current `n == n@pre`, `Zpower(10,0) = 1`, and `n@pre < n@pre + 1`.  The `n@pre <= INT_MAX` fact comes from the `by local` bridge while `n` still equals the original parameter.

Preservation: assuming `n > 0`, after `cnt++` and `n = n / 10`, quotient bounds for positive division by 10 preserve the interval facts.  `cnt + n <= n@pre` is preserved because the new quotient is at most the old positive `n - 1`, so `(cnt + 1) + (n / 10) <= cnt + n <= n@pre`.  The lower final digit bound for the next `cnt` follows from the old interval lower bound and `n >= 1`.

Exit: the loop exits with `n <= 0`; combined with `0 <= n`, this gives `n == 0`.  Since this path excluded the initial `n == 0` case, the invariant can prove `cnt > 0`, then the carried lower digit bound and interval upper bound with `n == 0` match `count_digits_spec(n@pre, cnt)`.
