# Fibonacci Mod

## 问题描述

实现一个函数，输入非负整数 `n` 和正整数 `mod`，返回第 `n` 个 Fibonacci 数对 `mod` 取模后的结果。

约定：

- `n >= 0`
- `mod > 0`
- `fib(0) = 0`
- `fib(1) = 1`
- 对 `n >= 2`，`fib(n) = fib(n - 1) + fib(n - 2)`
- 每一步都对 `mod` 取模

## 正确代码

```c
int fibonacci_mod(int n, int mod) {
    int i;
    int a = 0;
    int b = 1 % mod;
    int c;

    if (n == 0) {
        return 0;
    }

    for (i = 2; i <= n; ++i) {
        c = (a + b) % mod;
        a = b;
        b = c;
    }

    return b;
}
```

## 说明

这是 Fibonacci 的取模版本，适合验证“滚动状态 + 模运算保持范围”。
