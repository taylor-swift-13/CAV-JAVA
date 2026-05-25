# Array Second Largest

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回其中第二大的元素。

约定：

- `n >= 2`
- 数组长度恰好是 `n`
- 可以假设数组中所有元素互不相同
- 函数不修改数组

## 正确代码

```c
int array_second_largest(int n, int *a) {
    int i;
    int max1 = a[0];
    int max2 = a[1];

    if (max2 > max1) {
        int t = max1;
        max1 = max2;
        max2 = t;
    }

    for (i = 2; i < n; ++i) {
        if (a[i] > max1) {
            max2 = max1;
            max1 = a[i];
        } else if (a[i] > max2) {
            max2 = a[i];
        }
    }

    return max2;
}
```

## 说明

这道题适合验证“双状态量扫描”模式：

- 同时维护最大值和次大值
- 分支更新比单纯 max/min 更复杂
