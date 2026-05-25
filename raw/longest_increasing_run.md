# Longest Increasing Run

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回最长连续严格递增段的长度。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 空数组的结果为 `0`
- 函数不修改数组

## 正确代码

```c
int longest_increasing_run(int n, int *a) {
    int i;
    int cur;
    int best;

    if (n == 0) {
        return 0;
    }

    cur = 1;
    best = 1;
    for (i = 1; i < n; ++i) {
        if (a[i - 1] < a[i]) {
            cur++;
        } else {
            cur = 1;
        }
        if (best < cur) {
            best = cur;
        }
    }

    return best;
}
```

## 说明

这是经典线性 DP/扫描题，适合验证“当前连续段长度 + 历史最优长度”。
