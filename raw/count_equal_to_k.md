# Count Equal To K

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和整数 `k`，返回数组中等于 `k` 的元素个数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组

## 正确代码

```c
int count_equal_to_k(int n, int *a, int k) {
    int i;
    int ret = 0;

    for (i = 0; i < n; ++i) {
        if (a[i] == k) {
            ret++;
        }
    }

    return ret;
}
```

## 说明

这道题是最基础的数组计数题：

- 单层循环
- 循环内一个分支
- 不修改数组
