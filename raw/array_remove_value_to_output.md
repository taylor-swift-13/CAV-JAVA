# Array Remove Value To Output

## 问题描述

实现一个函数，把数组中所有不等于给定值 `k` 的元素按原顺序复制到输出数组，并返回复制的元素个数。

约定：
- `n` 表示输入数组长度，`n >= 0`。
- `a` 指向长度至少为 `n` 的输入数组。
- `out` 指向长度至少为 `n` 的输出数组。
- 输入数组 `a` 不需要被修改。

## 正确代码

```c
int array_remove_value_to_output(int n, int *a, int k, int *out) {
    int write = 0;
    int i = 0;
    while (i < n) {
        if (a[i] != k) {
            out[write] = a[i];
            write++;
        }
        i++;
    }
    return write;
}
```

## 说明

`write` 始终指向输出数组下一个可写位置。每遇到一个不等于 `k` 的元素，就把它复制到输出数组并推进 `write`。
