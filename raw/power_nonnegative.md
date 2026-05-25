# Power Nonnegative

## 问题描述

实现一个函数，输入整数 `base` 和非负整数 `exp`，返回 `base` 的 `exp` 次方。

约定：

- `exp >= 0`
- `base^0 = 1`
- 使用简单循环乘法，不使用快速幂

## 正确代码

```c
int power_nonnegative(int base, int exp) {
    int i;
    int ans = 1;

    for (i = 0; i < exp; ++i) {
        ans = ans * base;
    }

    return ans;
}
```

## 说明

这是最简单的幂运算题，适合验证“循环次数与累乘状态量”。
