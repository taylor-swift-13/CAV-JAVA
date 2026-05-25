# Count Digits

## 问题描述

实现一个函数，输入非负整数 `n`，返回它的十进制位数。

约定：

- `n >= 0`
- `count_digits(0) = 1`
- 对正数使用 `/ 10` 循环计数

## 正确代码

```c
int count_digits(int n) {
    int cnt = 0;

    if (n == 0) {
        return 1;
    }

    while (n > 0) {
        cnt++;
        n = n / 10;
    }

    return cnt;
}
```

## 说明

这是最简单的十进制位数统计题。
