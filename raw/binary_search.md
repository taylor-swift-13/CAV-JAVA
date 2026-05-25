# Binary Search

## 问题描述

实现一个函数，输入长度为 `n` 的非递减整数数组 `a` 和目标值 `target`，如果目标值存在，返回任意一个等于 `target` 的下标；如果不存在，返回 `-1`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 数组 `a` 非递减
- 函数不修改数组

## 正确代码

```c
int binary_search(int n, int *a, int target) {
    int left = 0;
    int right = n - 1;
    int mid;

    while (left <= right) {
        mid = left + (right - left) / 2;
        if (a[mid] == target) {
            return mid;
        }
        if (a[mid] < target) {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }

    return -1;
}
```

## 说明

这是最基础的二分查找题，适合验证“搜索区间收缩 + 区间外排除性质”。
