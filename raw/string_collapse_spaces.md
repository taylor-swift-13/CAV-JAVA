# String Collapse Spaces

## 问题描述

实现一个函数，把输入字符串中每一段连续空格压缩成一个空格，并写入输出字符串。

约定：
- `s` 是以 `'\0'` 结尾的输入字符串。
- `out` 指向足够大的输出缓冲区。
- 每一段一个或多个连续空格 `' '` 在输出中变成一个空格。
- 非空格字符保持原顺序。
- 输出字符串必须以 `'\0'` 结尾。

## 正确代码

```c
void string_collapse_spaces(char *s, char *out) {
    int i = 0;
    int j = 0;
    int in_space = 0;
    while (s[i] != '\0') {
        if (s[i] == ' ') {
            if (!in_space) {
                out[j] = ' ';
                j++;
                in_space = 1;
            }
        } else {
            out[j] = s[i];
            j++;
            in_space = 0;
        }
        i++;
    }
    out[j] = '\0';
}
```

## 说明

`in_space` 记录上一段输出是否已经写过空格。遇到连续空格时只写入第一个空格，遇到非空格字符时正常复制并清除空格状态。
