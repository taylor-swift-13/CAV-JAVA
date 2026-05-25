# String Replace Char

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，以及两个字符 `old_c` 和 `new_c`。把字符串中所有等于 `old_c` 的字符原地替换成 `new_c`。

约定：

- 字符串是合法的 C 风格字符串
- 函数原地修改字符串
- 终止符 `'\0'` 保持在原位置
- 对每个终止符前的下标 `i`，如果原来 `s[i] == old_c`，执行后 `s[i] == new_c`，否则保持原值

## 正确代码

```c
void string_replace_char(char *s, char old_c, char new_c) {
    int i = 0;

    while (s[i] != '\0') {
        if (s[i] == old_c) {
            s[i] = new_c;
        }
        i++;
    }
}
```

## 说明

这道题适合验证“字符串原地条件替换”的模式。
