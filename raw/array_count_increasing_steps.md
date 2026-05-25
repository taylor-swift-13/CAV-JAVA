# Array Count Increasing Steps

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，统计满足 `a[i] < a[i + 1]` 的下标个数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组

## 正确代码

```c
int array_count_increasing_steps(int n, int *a) {
    int i;
    int cnt = 0;

    for (i = 0; i + 1 < n; ++i) {
        if (a[i] < a[i + 1]) {
            cnt++;
        }
    }

    return cnt;
}
```

## 说明

这道题适合验证“相邻比较 + 条件计数”模式。
