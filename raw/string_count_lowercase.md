# String Count Lowercase

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，统计其中小写英文字母的个数。

约定：

- 输入是合法的 C 风格字符串
- 小写英文字母范围是 `'a'` 到 `'z'`
- 函数不修改字符串

## 正确代码

```c
int string_count_lowercase(char *s) {
    int i = 0;
    int cnt = 0;

    while (s[i] != '\0') {
        if (s[i] >= 'a' && s[i] <= 'z') {
            cnt++;
        }
        i++;
    }

    return cnt;
}
```

## 说明

这道题适合验证“字符串扫描 + 字符范围判断 + 计数”模式。
