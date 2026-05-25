# Annotation Reasoning

## Loop invariant for scalar stair-count DP

- Current program point: the only loop is `for (int i = 2; i <= n; i++)` in `annotated/verify_20260422_131939_climb_stairs.c`. The active annotated copy initially had no `Inv` before this `for`, so symbolic execution would have no loop-head summary connecting the scalar state variables `prev2`, `prev1`, and `cur` to the Coq function `climb_stairs_z`.
- Relevant unannotated code before the edit:

```c
int prev2 = 1;
int prev1 = 1;
int cur = 0;

for (int i = 2; i <= n; i++) {
    cur = prev1 + prev2;
    prev2 = prev1;
    prev1 = cur;
}

return cur;
```

- Since the `if (n <= 1) return 1;` branch has already returned before this loop, the loop path has `2 <= n` and the original precondition still gives `n <= 45`. At the loop-head control point, `i` is the next stair index to compute. Therefore `prev2` should equal `climb_stairs_z(i - 2)` and `prev1` should equal `climb_stairs_z(i - 1)`. On the first loop-head visit, `i == 2` and `cur == 0`, so `cur` cannot always equal the last computed result. After at least one completed body, `i > 2` and the assignment sequence makes `cur == prev1 == climb_stairs_z(i - 1)`.
- Planned invariant:

```c
/*@ Inv
      2 <= n && n <= 45 &&
      n == n@pre &&
      2 <= i && i <= n + 1 &&
      prev2 == climb_stairs_z(i - 2) &&
      prev1 == climb_stairs_z(i - 1) &&
      (i == 2 => cur == 0) &&
      (i > 2 => cur == climb_stairs_z(i - 1))
*/
for (int i = 2; i <= n; i++) {
    cur = prev1 + prev2;
    prev2 = prev1;
    prev1 = cur;
}
```

- Initialization: before the first condition check, `i == 2`, `prev2 == 1 == climb_stairs_z(0)`, `prev1 == 1 == climb_stairs_z(1)`, and `cur == 0`, so the `i == 2` implication supplies the initial `cur` state.
- Preservation: assuming the invariant at loop head and `i <= n`, the body computes `cur = climb_stairs_z(i - 1) + climb_stairs_z(i - 2)`, then shifts `prev2` to the old `prev1` and `prev1` to the new `cur`. At the next loop-head, `i` has advanced to `i + 1`, so the shifted values match `climb_stairs_z((i + 1) - 2)` and `climb_stairs_z((i + 1) - 1)`. The next `i` is greater than `2`, so the second `cur` implication records that `cur` is the latest computed count.
- Exit usability: when the loop exits, `i > n` and the invariant gives `i <= n + 1`, so `i == n + 1`. Because this path has `2 <= n`, we also have `i > 2`, and the invariant yields `cur == climb_stairs_z(i - 1) == climb_stairs_z(n)`, matching the function postcondition for the final `return cur`.
