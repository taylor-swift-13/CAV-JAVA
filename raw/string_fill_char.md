# String Fill Char

## 问题描述

实现一个函数，输入整数 `n`、字符 `c` 和缓冲区 `s`。把前 `n` 个位置全部写成 `c`，最后一个位置写终止符。

约定：

- `n >= 0`
- `s` 缓冲区长度至少是 `n + 1`
- 需要原地写入字符串

## 正确代码

```c
void string_fill_char(int n, char c, char *s) {
    int i;

    for (i = 0; i < n; ++i) {
        s[i] = c;
    }
    s[n] = '\0';
}
```

## 说明

这道题适合验证“字符缓冲区批量填充”模式。
