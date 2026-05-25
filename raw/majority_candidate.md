# Majority Candidate

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回 Boyer-Moore 投票算法得到的候选多数元素。

约定：

- `n >= 1`
- `a` 的长度恰好是 `n`
- 题目只要求返回候选值，不要求在函数中验证它一定出现超过一半
- 函数不修改数组

## 正确代码

```c
int majority_candidate(int n, int *a) {
    int i;
    int candidate = a[0];
    int count = 1;

    for (i = 1; i < n; ++i) {
        if (count == 0) {
            candidate = a[i];
            count = 1;
        } else if (a[i] == candidate) {
            count++;
        } else {
            count--;
        }
    }

    return candidate;
}
```

## 说明

这是经典 Boyer-Moore 投票算法，适合验证“候选值 + 抵消计数”的状态更新。
