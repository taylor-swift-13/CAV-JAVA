# Array Longest Nonnegative Run

## 问题描述

实现一个函数，返回数组中最长连续非负元素段的长度。

约定：
- `n` 表示数组长度，`n >= 0`。
- `a` 指向长度至少为 `n` 的整数数组。
- 非负元素指 `a[i] >= 0`。
- 如果数组中没有非负元素，返回 `0`。

## 正确代码

```c
int array_longest_nonnegative_run(int n, int *a) {
    int best = 0;
    int current = 0;
    int i = 0;
    while (i < n) {
        if (a[i] >= 0) {
            current++;
            if (current > best) {
                best = current;
            }
        } else {
            current = 0;
        }
        i++;
    }
    return best;
}
```

## 说明

`current` 记录以当前位置结尾的连续非负段长度，`best` 记录目前见过的最大长度。遇到负数时当前段被清空。
