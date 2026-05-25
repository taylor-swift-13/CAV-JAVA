# Merge Sorted Arrays

## 问题描述

实现一个函数，输入两个非递减整数数组 `a`、`b`，长度分别为 `n`、`m`，把合并后的非递减结果写入长度为 `n + m` 的输出数组 `out`。

约定：

- `n >= 0`
- `m >= 0`
- `a` 的长度恰好是 `n`
- `b` 的长度恰好是 `m`
- `out` 的长度恰好是 `n + m`
- `a` 和 `b` 都非递减
- 函数不修改 `a` 和 `b`

## 正确代码

```c
void merge_sorted_arrays(int n, int *a, int m, int *b, int *out) {
    int i = 0;
    int j = 0;
    int k = 0;

    while (i < n && j < m) {
        if (a[i] <= b[j]) {
            out[k] = a[i];
            i++;
        } else {
            out[k] = b[j];
            j++;
        }
        k++;
    }

    while (i < n) {
        out[k] = a[i];
        i++;
        k++;
    }

    while (j < m) {
        out[k] = b[j];
        j++;
        k++;
    }
}
```

## 说明

这是经典归并过程，适合验证“三指针 + 输出前缀合并语义”。
