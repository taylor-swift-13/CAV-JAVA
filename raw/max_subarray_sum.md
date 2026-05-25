# Max Subarray Sum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回非空连续子数组的最大和。

约定：

- `n >= 1`
- `a` 的长度恰好是 `n`
- 函数不修改数组
- 使用 Kadane 算法

## 正确代码

```c
int max_subarray_sum(int n, int *a) {
    int i;
    int cur = a[0];
    int best = a[0];

    for (i = 1; i < n; ++i) {
        if (cur + a[i] < a[i]) {
            cur = a[i];
        } else {
            cur = cur + a[i];
        }
        if (best < cur) {
            best = cur;
        }
    }

    return best;
}
```

## 说明

这是经典 Kadane 动态规划题，适合验证“当前后缀最优 + 全局最优”两个状态量。
