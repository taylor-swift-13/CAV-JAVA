# Count Positive

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回其中严格大于 `0` 的元素个数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组

## 正确代码

```c
int count_positive(int n, int *a) {
    int i;
    int cnt = 0;

    for (i = 0; i < n; ++i) {
        if (a[i] > 0) {
            cnt++;
        }
    }

    return cnt;
}
```

## 说明

这道题适合验证“扫描 + 条件计数”模式：

- 单层循环
- 一个累加状态量
- 循环中不修改输入数组
