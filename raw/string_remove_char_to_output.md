# String Remove Char To Output

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`、输出数组 `out` 和字符 `c`。把 `s` 中所有不等于 `c` 的字符按原顺序复制到 `out`，最后写入结尾字符 `'\0'`，返回输出字符串的长度。

约定：

- 输入 `s` 是合法的 C 风格字符串
- `out` 有足够空间保存结果和结尾字符
- 函数不修改 `s`

## 正确代码

```c
int string_remove_char_to_output(char *s, char *out, char c) {
    int i = 0;
    int j = 0;

    while (s[i] != '\0') {
        if (s[i] != c) {
            out[j] = s[i];
            j++;
        }
        i++;
    }

    out[j] = '\0';
    return j;
}
```

## 说明

这道题适合验证“双下标字符串扫描 + 条件复制 + 输出长度”模式。
