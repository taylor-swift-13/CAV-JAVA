# String Count Spaces

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，统计其中空格字符 `' '` 的个数。

约定：

- 输入是合法的 C 风格字符串
- 只统计普通空格字符，不统计制表符或换行符
- 函数不修改字符串

## 正确代码

```c
int string_count_spaces(char *s) {
    int i = 0;
    int cnt = 0;

    while (s[i] != '\0') {
        if (s[i] == ' ') {
            cnt++;
        }
        i++;
    }

    return cnt;
}
```

## 说明

这道题适合验证“字符串扫描 + 单字符条件计数”模式。
