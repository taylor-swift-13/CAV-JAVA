# Array Count Greater Than K

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和整数 `k`，返回数组中严格大于 `k` 的元素个数。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组

## 正确代码

```c
int array_count_greater_than_k(int n, int *a, int k) {
    int i;
    int cnt = 0;

    for (i = 0; i < n; ++i) {
        if (a[i] > k) {
            cnt++;
        }
    }

    return cnt;
}
```

## 说明

这道题适合验证“数组扫描 + 阈值条件计数”模式。
