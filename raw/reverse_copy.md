# Reverse Copy

## 问题描述

实现一个函数，把长度为 `n` 的整数数组 `src` 逆序复制到长度为 `n` 的整数数组 `dst`。

约定：

- `n >= 0`
- `src` 和 `dst` 长度都恰好是 `n`
- 函数读取 `src`，写入 `dst`

## 正确代码

```c
void reverse_copy(int n, int *src, int *dst) {
    int i;

    for (i = 0; i < n; ++i) {
        dst[i] = src[n - 1 - i];
    }
}
```

## 说明

这道题是最基础的逆序数组构造：

- 单层循环
- 一个读、一个写
- 不修改源数组
