# Array Last Positive

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回最后一个正数元素的下标；如果不存在正数，返回 `-1`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组

## 正确代码

```c
int array_last_positive(int n, int *a) {
    int i;
    int ans = -1;

    for (i = 0; i < n; ++i) {
        if (a[i] > 0) {
            ans = i;
        }
    }

    return ans;
}
```

## 说明

这道题适合验证“扫描状态量保存最后一次命中位置”模式。
