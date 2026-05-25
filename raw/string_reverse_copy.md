# String Reverse Copy

## 问题描述

实现一个函数，输入一个长度为 `n` 的字符串 `src` 和一个长度为 `n + 1` 的输出缓冲区 `dst`，把 `src` 逆序复制到 `dst`，并补上终止符。

约定：

- `src` 是合法的 C 风格字符串
- `dst` 缓冲区长度足够
- 函数不修改 `src`
- 执行后 `dst` 也是合法的 C 风格字符串

## 正确代码

```c
void string_reverse_copy(int n, char *src, char *dst) {
    int i;

    for (i = 0; i < n; ++i) {
        dst[i] = src[n - 1 - i];
    }
    dst[n] = '\0';
}
```

## 说明

这道题适合验证“只读输入字符串 + 顺序写输出缓冲区”模式。
