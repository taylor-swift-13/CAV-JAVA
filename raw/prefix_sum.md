# Prefix Sum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和长度为 `n` 的整数数组 `out`，把前缀和写入 `out`。

约定：

- `n >= 0`
- `a` 和 `out` 长度都恰好是 `n`
- `out[i] = a[0] + a[1] + ... + a[i]`

## 正确代码

```c
void prefix_sum(int n, int *a, int *out) {
    int i;
    int acc = 0;

    for (i = 0; i < n; ++i) {
        acc += a[i];
        out[i] = acc;
    }
}
```

## 说明

这道题是最基础的前缀和构造：

- 单层循环
- 一个累加器
- 读数组并写数组
