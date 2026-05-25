# Array Maximum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回数组中的最大值。

约定：

- `n >= 1`
- 数组长度恰好是 `n`
- 函数只读数组，不修改数组内容

## 正确代码

```c
int array_max(int n, int *a) {
    int i;
    int ret = a[0];

    for (i = 1; i < n; ++i) {
        if (a[i] > ret) {
            ret = a[i];
        }
    }

    return ret;
}
```

## 说明

这是一道很基础的数组扫描题：

- 单层循环
- 一个循环内分支
- 不修改数组 shape
- invariant 需要表达“`ret` 是当前已扫描前缀的最大值”
