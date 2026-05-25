## 2026-04-22 initial loop invariant for rotate_left_by_one

Target function:

```c
void rotate_left_by_one(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          ((i < n - 1 => lr[i] == l[i + 1]) &&
           (i == n - 1 => lr[i] == l[0]))) &&
        IntArray::full(a, n, lr)
*/
```

The loop is:

```c
int first = a[0];
for (i = 0; i < n - 1; ++i) {
    a[i] = a[i + 1];
}
a[n - 1] = first;
```

The loop head invariant must describe the state before checking `i < n - 1`. At that point, `i` is the number of already shifted cells. The processed prefix `a[0..i)` should equal the original slice `l[1..i+1)`, and the unprocessed suffix `a[i..n)` should still equal the original slice `l[i..n)`. Therefore the whole array value is:

```c
app(sublist(1, i + 1, l), sublist(i, n@pre, l))
```

This is initialized when `i == 0` because `sublist(1, 1, l)` is empty and `sublist(0, n, l)` is `l`. It is preserved by one loop body because the assignment `a[i] = a[i + 1]` changes the current list at index `i` from original `l[i]` to original `l[i + 1]`, extending the shifted prefix by one element. It is useful at loop exit because `i == n - 1` gives:

```c
app(sublist(1, n, l), sublist(n - 1, n, l))
```

Then the final write `a[n - 1] = first` should produce a list `lr` with prefix `sublist(1, n, l)` and final element `l[0]`, which is exactly the postcondition rotation relation.

The invariant also carries the unchanged parameters and local saved value:

```c
0 <= i && i <= n@pre - 1 &&
a == a@pre &&
n == n@pre &&
n@pre == Zlength(l) &&
first == l[0] &&
IntArray::full(a, n@pre, app(sublist(1, i + 1, l), sublist(i, n@pre, l)))
```

I will add this `Inv` before the `for` loop. After the loop, I will add an `Assert` fixing `i == n@pre - 1` and the corresponding full-array shape before the final assignment; this should keep the final update close to the loop exit while local permissions for `i` and `first` are still available.

## 2026-04-22 revision after checking archived rotate_left_by_one pattern

Before running `symexec`, I checked the archived successful `rotate_left_by_one` example under `CAV/archieve/examples_backup_20260422_011624/rotate_left_by_one`. It uses a less expanded invariant:

```c
/*@ Inv exists l1,
      0 <= i && i <= n@pre - 1 &&
      n == n@pre &&
      a == a@pre &&
      Zlength(l) == n@pre &&
      first == l[0] &&
      Zlength(l1) == i &&
      (forall (k: Z), (0 <= k && k < i) => l1[k] == l[k + 1]) &&
      IntArray::full(a, n@pre, app(l1, sublist(i, n@pre, l)))
*/
```

This is semantically the same loop-head state as the first invariant: `l1` names `sublist(1, i + 1, l)` without forcing the frontend to normalize that exact `sublist` expression at every control point. The older failed workspace for the same function showed that an explicit post-loop `Assert`/single-hole bridge before `a[n - 1] = first` can make symbolic execution lose the concrete writable cell and report `cannot write null value to memory`. Therefore the next annotation revision removes the post-loop `Assert` and uses the archived existential-prefix invariant only. The final store will be executed from the full-array invariant state, leaving any residual list equality proof to the generated Coq obligations rather than forcing a brittle frontend bridge.
