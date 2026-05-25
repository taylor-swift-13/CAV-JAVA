# Array Count Zero

## 问题描述

实现一个函数，统计长度为 `n` 的整数数组中等于 `0` 的元素个数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组
- 返回值等于数组中满足 `a[i] == 0` 的下标数量

## 正确代码

```c
int array_count_zero(int n, int *a) {
    int i;
    int count = 0;

    for (i = 0; i < n; ++i) {
        if (a[i] == 0) {
            count++;
        }
    }

    return count;
}
```

## 说明

这道题适合验证“条件计数”的数组扫描模式。
