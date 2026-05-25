# Array Pairwise Sum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和 `b`，以及长度为 `n` 的输出数组 `out`。对每个下标 `i`，写入 `out[i] = a[i] + b[i]`。

约定：

- `n >= 0`
- `a`、`b` 和 `out` 的长度都恰好是 `n`
- 函数不修改 `a` 和 `b`

## 正确代码

```c
void array_pairwise_sum(int n, int *a, int *b, int *out) {
    int i;

    for (i = 0; i < n; ++i) {
        out[i] = a[i] + b[i];
    }
}
```

## 说明

这道题适合验证“两个输入数组逐点计算输出数组”模式。
