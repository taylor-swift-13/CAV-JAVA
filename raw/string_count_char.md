# String Count Char

## 问题描述

实现一个函数，输入字符串 `s` 和字符 `c`，返回 `s` 中字符 `c` 出现的次数。

约定：

- `s` 是合法的以 `'\0'` 结尾的字符串
- 函数不修改字符串

## 正确代码

```c
int string_count_char(char *s, char c) {
    int i = 0;
    int ret = 0;

    while (s[i] != '\0') {
        if (s[i] == c) {
            ret++;
        }
        i++;
    }

    return ret;
}
```

## 说明

这道题是最基础的字符串计数：

- 单层循环
- 一个分支
- 只读字符串
