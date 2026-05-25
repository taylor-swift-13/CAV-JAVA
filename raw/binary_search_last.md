# Binary Search Last

## 问题描述

实现一个函数，输入长度为 `n` 的非递减整数数组 `a` 和目标值 `target`，返回最后一个等于 `target` 的下标；如果不存在，返回 `-1`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 数组 `a` 非递减
- 函数不修改数组

## 正确代码

```c
int binary_search_last(int n, int *a, int target) {
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

    if (left > 0 && a[left - 1] == target) {
        return left - 1;
    }
    return -1;
}
```

## 说明

这是 upper_bound 的直接应用，适合验证“边界二分 + 前一位检查”。
