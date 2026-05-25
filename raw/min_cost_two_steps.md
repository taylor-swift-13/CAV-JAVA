# Min Cost Two Steps

## 问题描述

实现一个函数，输入长度为 `n` 的非负整数数组 `cost`，每次可以向前走一步或两步，返回走到下标 `n - 1` 的最小代价。进入下标 `i` 的代价是 `cost[i]`。

约定：

- `n >= 1`
- `cost` 的长度恰好是 `n`
- 所有 `cost[i] >= 0`
- 起点在下标 `0`
- 函数不修改数组

## 正确代码

```c
int min_cost_two_steps(int n, int *cost) {
    int i;
    int prev2;
    int prev1;
    int cur;

    if (n == 1) {
        return cost[0];
    }

    prev2 = cost[0];
    prev1 = cost[0] + cost[1];

    for (i = 2; i < n; ++i) {
        if (prev1 < prev2) {
            cur = prev1 + cost[i];
        } else {
            cur = prev2 + cost[i];
        }
        prev2 = prev1;
        prev1 = cur;
    }

    return prev1;
}
```

## 说明

这是最简单的线性 DP 最小值问题，适合验证“状态量表示前两个位置最优解”。
