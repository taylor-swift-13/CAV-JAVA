# Count Divisors

## 问题描述

实现一个函数，输入正整数 `n`，返回 `n` 的正约数个数。

约定：

- `n >= 1`
- 如果 `d` 满足 `1 <= d <= n` 且 `n % d == 0`，则 `d` 是 `n` 的正约数

## 正确代码

```c
int count_divisors(int n) {
    int d;
    int cnt = 0;

    for (d = 1; d <= n; ++d) {
        if (n % d == 0) {
            cnt++;
        }
    }

    return cnt;
}
```

## 说明

这是最简单的约数计数题，适合验证“数论条件计数 + 循环边界”。
