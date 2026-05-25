# Array Any Negative

## 问题描述

实现一个函数，判断长度为 `n` 的整数数组中是否存在负数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组
- 如果存在某个下标 `i` 满足 `a[i] < 0`，返回 `1`
- 否则返回 `0`

## 正确代码

```c
int array_any_negative(int n, int *a) {
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] < 0) {
            return 1;
        }
    }

    return 0;
}
```

## 说明

这道题适合验证“数组扫描 + 早返回”的存在性判断模式。
