# Two Sum Sorted

## 问题描述

实现一个函数，输入长度为 `n` 的非递减整数数组 `a` 和目标值 `target`，判断是否存在两个不同下标 `i < j`，使得 `a[i] + a[j] == target`。如果存在返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 数组 `a` 非递减
- 函数不修改数组
- 返回值只使用 `0` 或 `1`

## 正确代码

```c
int two_sum_sorted(int n, int *a, int target) {
    int left = 0;
    int right = n - 1;
    int s;

    while (left < right) {
        s = a[left] + a[right];
        if (s == target) {
            return 1;
        }
        if (s < target) {
            left++;
        } else {
            right--;
        }
    }

    return 0;
}
```

## 说明

这是经典双指针题，适合验证“有序数组两端收缩搜索区间”。
