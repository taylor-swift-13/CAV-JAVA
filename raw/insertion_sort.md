# Insertion Sort

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，用插入排序将数组原地排成非递减顺序。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数原地修改数组

## 正确代码

```c
void insertion_sort(int n, int *a) {
    int i;
    int j;
    int key;

    for (i = 1; i < n; ++i) {
        key = a[i];
        j = i - 1;
        while (j >= 0 && a[j] > key) {
            a[j + 1] = a[j];
            j--;
        }
        a[j + 1] = key;
    }
}
```

## 说明

这是经典插入排序题，适合验证“有序前缀 + 元素右移 + 插入位置”。
