# Fibonacci

## 问题描述

实现一个函数，输入整数 `n`，返回第 `n` 个 Fibonacci 数。

约定：

- `n >= 0`
- `fib(0) = 0`
- `fib(1) = 1`
- 对 `n >= 2`，`fib(n) = fib(n - 1) + fib(n - 2)`

## 正确代码

```c
int fibonacci(int n) {
    int i;
    int a = 0;
    int b = 1;
    int c;

    if (n == 0) {
        return 0;
    }

    for (i = 2; i <= n; ++i) {
        c = a + b;
        a = b;
        b = c;
    }

    return b;
}
```

## 说明

这是最简单的动态规划题之一，适合验证“两状态滚动数组”的循环不变量。
