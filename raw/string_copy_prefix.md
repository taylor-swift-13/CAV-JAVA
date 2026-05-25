# String Copy Prefix

## 问题描述

实现一个函数，输入长度为 `n` 的字符串 `src`、整数 `k` 和输出缓冲区 `dst`。把 `src` 的前 `k` 个字符复制到 `dst`，然后补一个终止符。

约定：

- `0 <= k <= n`
- `src` 是长度为 `n` 的合法 C 风格字符串
- `dst` 缓冲区长度至少是 `k + 1`
- 函数不修改 `src`

## 正确代码

```c
void string_copy_prefix(int k, char *src, char *dst) {
    int i;

    for (i = 0; i < k; ++i) {
        dst[i] = src[i];
    }
    dst[k] = '\0';
}
```

## 说明

这道题适合验证“固定前缀复制 + 末尾补终止符”模式。
