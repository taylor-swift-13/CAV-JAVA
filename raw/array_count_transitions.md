# Array Count Transitions

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，统计相邻元素发生变化的次数。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组
- 对每个 `i >= 1`，如果 `a[i] != a[i - 1]`，则计数加一

## 正确代码

```c
int array_count_transitions(int n, int *a) {
    int i;
    int cnt = 0;

    for (i = 1; i < n; ++i) {
        if (a[i] != a[i - 1]) {
            cnt++;
        }
    }

    return cnt;
}
```

## 说明

这道题适合验证“相邻元素比较 + 条件计数”模式。
