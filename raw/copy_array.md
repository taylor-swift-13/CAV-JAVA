# Copy Array

## 问题描述

实现一个函数，把长度为 `n` 的整数数组 `src` 复制到长度为 `n` 的整数数组 `dst`。

约定：

- `n >= 0`
- `src` 和 `dst` 长度都恰好是 `n`
- 函数读取 `src`，写入 `dst`

## 正确代码

```c
void copy_array(int n, int *src, int *dst) {
    int i;

    for (i = 0; i < n; ++i) {
        dst[i] = src[i];
    }
}
```

## 说明

这道题是最基础的双数组扫描：

- 单层循环
- 一个读、一个写
- 不涉及复杂数据结构
- invariant 适合写成“`dst` 已写前缀等于 `src` 对应前缀”
