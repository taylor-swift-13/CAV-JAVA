# Array Copy Positive

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和长度为 `n` 的输出数组 `out`。如果 `a[i]` 是正数，则 `out[i] = a[i]`；否则 `out[i] = 0`。

约定：

- `n >= 0`
- `a` 和 `out` 的长度都恰好是 `n`
- 函数不修改 `a`

## 正确代码

```c
void array_copy_positive(int n, int *a, int *out) {
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] > 0) {
            out[i] = a[i];
        } else {
            out[i] = 0;
        }
    }
}
```

## 说明

这道题适合验证“输入数组到输出数组的条件映射”模式。
