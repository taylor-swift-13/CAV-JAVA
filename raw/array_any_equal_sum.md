# Array Any Equal Sum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，以及整数 `x` 和 `y`，判断数组中是否存在元素等于 `x + y`。如果存在返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组
- 返回值只使用 `0` 或 `1`

## 正确代码

```c
int array_any_equal_sum(int n, int *a, int x, int y) {
    int i;
    int target = x + y;

    for (i = 0; i < n; ++i) {
        if (a[i] == target) {
            return 1;
        }
    }

    return 0;
}
```

## 说明

这道题适合验证“目标值预计算 + 数组存在性判断”模式。
