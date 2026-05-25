# Upper Bound

## 问题描述

实现一个函数，输入长度为 `n` 的非递减整数数组 `a` 和目标值 `target`，返回第一个满足 `a[i] > target` 的下标；如果不存在，返回 `n`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 数组 `a` 非递减
- 函数不修改数组

## 正确代码

```c
int upper_bound(int n, int *a, int target) {
    int left = 0;
    int right = n;
    int mid;

    while (left < right) {
        mid = left + (right - left) / 2;
        if (a[mid] <= target) {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    return left;
}
```

## 说明

这是最基础的 `upper_bound` 边界二分题。
