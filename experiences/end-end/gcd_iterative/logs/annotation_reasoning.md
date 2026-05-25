## 2026-04-22 initial loop invariant

Current program point:

```c
int r;

while (b != 0) {
    r = a % b;
    a = b;
    b = r;
}

return a;
```

The target postcondition is:

```c
gcd_iterative_spec(a@pre, b@pre, __return) && emp
```

The loop mutates both `a` and `b`, so the postcondition cannot be recovered from simple parameter-preservation facts. The semantic fact that must survive every loop iteration is that the gcd of the current pair `(a, b)` is the same as the gcd of the original pair `(a@pre, b@pre)`. Because the imported contract exposes the relation `gcd_iterative_spec : Z -> Z -> Z -> Prop`, the invariant will preserve this fact by existentially naming the shared gcd value:

```c
/*@ Inv exists g,
      0 <= a &&
      0 <= b &&
      0 < a + b &&
      gcd_iterative_spec(a@pre, b@pre, g) &&
      gcd_iterative_spec(a, b, g)
*/
while (b != 0) {
    r = a % b;
    a = b;
    b = r;
}
```

Initialization: choose `g = Z.gcd a@pre b@pre`. The precondition gives `0 <= a`, `0 <= b`, and `0 < a + b`; both spec facts reduce to the same gcd definition from `input/gcd_iterative.v`.

Preservation: at the loop head, `0 <= b` and `b != 0` imply `0 < b`, so C modulo produces `r = a % b` with `0 <= r < b`. After the body, the next current pair is `(old b, old a mod old b)`. The Euclidean property `Z.gcd old_a old_b = Z.gcd old_b (old_a mod old_b)` preserves the same witness `g`. Nonnegativity is preserved by `old b >= 0` and modulo nonnegativity, and `0 < new_a + new_b` follows from `new_a = old_b > 0`.

Exit usability: when the loop exits, `b == 0`; the invariant gives a shared `g` with `gcd_iterative_spec(a, 0, g)`. Since `0 <= a`, the definition of `Z.gcd` gives `g = a`, so `return a` can satisfy `gcd_iterative_spec(a@pre, b@pre, __return)`.
