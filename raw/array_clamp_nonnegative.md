# Array Clamp Nonnegative

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`。把所有负数元素改成 `0`，非负元素保持不变。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 需要原地修改数组

## 正确代码

```c
void array_clamp_nonnegative(int n, int *a) {
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] < 0) {
            a[i] = 0;
        }
    }
}
```

## 说明

这道题适合验证“条件式原地修正”模式。
