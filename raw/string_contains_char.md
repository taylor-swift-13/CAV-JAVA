# String Contains Char

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s` 和一个字符 `c`，判断字符串中是否出现过这个字符。

约定：

- 字符串是合法的 C 风格字符串
- 函数不修改字符串
- 如果某个位置满足 `s[i] == c`，返回 `1`
- 否则返回 `0`

## 正确代码

```c
int string_contains_char(char *s, char c) {
    int i = 0;

    while (s[i] != '\0') {
        if (s[i] == c) {
            return 1;
        }
        i++;
    }

    return 0;
}
```

## 说明

这道题适合验证“扫描字符串直到 terminator”模式：

- 单层循环
- 只读字符串
- 命中后立即返回
