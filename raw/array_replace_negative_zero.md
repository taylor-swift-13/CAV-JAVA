# Array Replace Negative Zero

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，把所有负数原地改为 `0`，非负数保持不变。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数会修改数组 `a`

## 正确代码

```c
void array_replace_negative_zero(int n, int *a) {
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] < 0) {
            a[i] = 0;
        }
    }
}
```

## 说明

这道题适合验证“原地数组更新 + 条件保持原值”模式。
