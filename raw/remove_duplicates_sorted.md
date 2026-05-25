# Remove Duplicates Sorted

## 问题描述

实现一个函数，输入长度为 `n` 的非递减整数数组 `a`，原地删除重复元素，使每个不同元素只保留一次，并返回新长度。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 数组 `a` 非递减
- 函数可以修改数组前缀

## 正确代码

```c
int remove_duplicates_sorted(int n, int *a) {
    int i;
    int j;

    if (n == 0) {
        return 0;
    }

    j = 1;
    for (i = 1; i < n; ++i) {
        if (a[i] != a[j - 1]) {
            a[j] = a[i];
            j++;
        }
    }

    return j;
}
```

## 说明

这是经典双指针原地压缩题，适合验证“输出前缀是不重复摘要”。
