# Tribonacci

## 问题描述

实现一个函数，输入整数 `n`，返回第 `n` 个 Tribonacci 数。

约定：

- `n >= 0`
- `tri(0) = 0`
- `tri(1) = 1`
- `tri(2) = 1`
- 对 `n >= 3`，`tri(n) = tri(n - 1) + tri(n - 2) + tri(n - 3)`

## 正确代码

```c
int tribonacci(int n) {
    int i;
    int a = 0;
    int b = 1;
    int c = 1;
    int d;

    if (n == 0) {
        return 0;
    }
    if (n == 1) {
        return 1;
    }

    for (i = 3; i <= n; ++i) {
        d = a + b + c;
        a = b;
        b = c;
        c = d;
    }

    return c;
}
```

## 说明

这是 Fibonacci 的三状态版本，适合验证“固定数量状态量滚动更新”。
