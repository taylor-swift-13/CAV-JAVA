# Climbing Stairs

## 问题描述

给定一个非负整数 `n`，表示爬到第 `n` 阶台阶。

每次你只能爬 `1` 阶或者 `2` 阶。请返回一共有多少种不同的方法可以爬到第 `n` 阶。

约定：
- `n = 0` 时返回 `1`，表示什么都不做也算一种方式。
- `n = 1` 时返回 `1`。
- 输入 `n` 为非负整数。

## 正确代码

```c
int climbStairs(int n) {
    if (n <= 1) return 1;
    int prev2 = 1; // 代表 dp[i-2]
    int prev1 = 1; // 代表 dp[i-1]
    int cur = 0;

    for (int i = 2; i <= n; i++) {
        cur = prev1 + prev2;
        prev2 = prev1;
        prev1 = cur;
    }
    return cur;
}
```

## 说明

这段代码使用滚动变量实现斐波那契式动态规划：
- `prev2` 保存到前两阶的方法数
- `prev1` 保存到前一阶的方法数
- `cur` 保存当前阶的方法数

最终返回爬到第 `n` 阶的方法总数。
