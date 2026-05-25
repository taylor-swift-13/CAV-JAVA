# Array Prefix Max

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和长度为 `n` 的输出数组 `out`。对每个下标 `i`，把前缀 `a[0..i]` 的最大值写到 `out[i]`。

约定：

- `n >= 0`
- `a` 和 `out` 的长度都恰好是 `n`
- 函数不修改 `a`

## 正确代码

```c
void array_prefix_max(int n, int *a, int *out) {
    int i;
    int cur;

    if (n == 0) {
        return;
    }

    cur = a[0];
    out[0] = cur;
    for (i = 1; i < n; ++i) {
        if (a[i] > cur) {
            cur = a[i];
        }
        out[i] = cur;
    }
}
```

## 说明

这道题适合验证“扫描状态量 + 输出数组逐步写入”模式。
