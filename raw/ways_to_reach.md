# Ways To Reach

## 问题描述

实现一个函数，输入非负整数 `n`，每次可以走 `1` 步或 `2` 步，返回到达第 `n` 级台阶的方法数。

约定：

- `n >= 0`
- `ways(0) = 1`
- `ways(1) = 1`
- 对 `n >= 2`，`ways(n) = ways(n - 1) + ways(n - 2)`

## 正确代码

```c
int ways_to_reach(int n) {
    int i;
    int a = 1;
    int b = 1;
    int c;

    if (n == 0) {
        return 1;
    }

    for (i = 2; i <= n; ++i) {
        c = a + b;
        a = b;
        b = c;
    }

    return b;
}
```

## 说明

这是最简单的台阶 DP，和 Fibonacci 类似但初值不同。
