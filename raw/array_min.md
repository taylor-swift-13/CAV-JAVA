# Array Minimum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回数组中的最小值。

约定：

- `n >= 1`
- 数组长度恰好是 `n`
- 函数只读数组，不修改数组内容

## 正确代码

```c
int array_min(int n, int *a) {
    int i;
    int ret = a[0];

    for (i = 1; i < n; ++i) {
        if (a[i] < ret) {
            ret = a[i];
        }
    }

    return ret;
}
```

## 说明

这道题和 `array_max` 对称：

- 单层循环
- 循环内一个分支
- 不修改数组
- invariant 适合写成“`ret` 是当前已扫描前缀的最小值”
