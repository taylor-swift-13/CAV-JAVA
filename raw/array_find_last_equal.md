# Array Find Last Equal

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和整数 `k`，返回最后一个满足 `a[i] == k` 的下标。如果不存在这样的元素，返回 `-1`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组
- 如果存在多个匹配位置，返回最大的匹配下标

## 正确代码

```c
int array_find_last_equal(int n, int *a, int k) {
    int i;
    int ans = -1;

    for (i = 0; i < n; ++i) {
        if (a[i] == k) {
            ans = i;
        }
    }

    return ans;
}
```

## 说明

这道题适合验证“扫描并维护最后一次命中位置”的模式。
