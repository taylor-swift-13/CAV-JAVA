# ABS

Implement an absolute-value function in Java.

Target method:

```java
public static int abs(int x)
```

Behavior:

- If `x >= 0`, return `x`.
- If `x < 0`, return `-x`.

Requirements:

- Exclude `Integer.MIN_VALUE`, because `-Integer.MIN_VALUE` overflows an `int`.
- The method must be deterministic and must not mutate any state.
- The generated Java class should be named `Abs`.
- The implementation should be simple enough for OpenJML ESC to verify.
