# Array First Negative

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回第一个负数元素的下标；如果不存在负数，返回 `-1`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组

## 正确代码

```c
int array_first_negative(int n, int *a) {
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] < 0) {
            return i;
        }
    }

    return -1;
}
```

## 说明

这道题适合验证“提前返回 + 前缀中不存在目标元素”模式。
