# Clamp Nonnegative

Implement a Java method that clamps a single integer to the nonnegative range.

Target method:

```java
public static int clamp_nonnegative(int x)
```

Behavior:

- If `x >= 0`, return `x`.
- If `x < 0`, return `0`.

Requirements:

- The generated Java class should be named `ClampNonnegative`.
- The method must be deterministic.
- The method must not mutate any state.
- The implementation should be simple enough for OpenJML ESC to verify.
