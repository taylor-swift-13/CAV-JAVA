# String Count Vowels

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，统计其中元音字母 `a e i o u` 的出现次数。

约定：

- 输入是合法的 C 风格字符串
- 函数不修改字符串

## 正确代码

```c
int string_count_vowels(char *s) {
    int i = 0;
    int cnt = 0;

    while (s[i] != '\0') {
        if (s[i] == 'a' || s[i] == 'e' || s[i] == 'i' ||
            s[i] == 'o' || s[i] == 'u') {
            cnt++;
        }
        i++;
    }

    return cnt;
}
```

## 说明

这道题适合验证“字符串扫描 + 多分支命中条件”模式。
