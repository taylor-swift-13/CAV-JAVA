# String Count Words Simple

## 问题描述

实现一个函数，统计以 `'\0'` 结尾的字符串中单词的个数。

约定：
- 字符串由普通字符、空格字符 `' '` 和结尾字符 `'\0'` 组成。
- 单词是一个或多个连续的非空格字符。
- 多个连续空格不产生空单词。
- 前导空格和尾随空格不产生额外单词。

## 正确代码

```c
int string_count_words_simple(char *s) {
    int count = 0;
    int in_word = 0;
    int i = 0;
    while (s[i] != '\0') {
        if (s[i] == ' ') {
            in_word = 0;
        } else {
            if (!in_word) {
                count++;
                in_word = 1;
            }
        }
        i++;
    }
    return count;
}
```

## 说明

`in_word` 记录当前位置之前是否已经处在一个单词内部。只有从空格状态进入非空格状态时，才把单词数加一。
