# Selection Sort

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，用选择排序将数组原地排成非递减顺序。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数原地修改数组

## 正确代码

```c
void selection_sort(int n, int *a) {
    int i;
    int j;
    int min_idx;
    int tmp;

    for (i = 0; i < n; ++i) {
        min_idx = i;
        for (j = i + 1; j < n; ++j) {
            if (a[j] < a[min_idx]) {
                min_idx = j;
            }
        }
        tmp = a[i];
        a[i] = a[min_idx];
        a[min_idx] = tmp;
    }
}
```

## 说明

这是经典简单排序题，适合验证“已排序前缀 + 剩余区间最小值选择”。
