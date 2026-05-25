# Array Replace K

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`、整数 `old_k` 和 `new_k`，把数组中所有等于 `old_k` 的元素替换成 `new_k`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 需要原地修改数组

## 正确代码

```c
void array_replace_k(int n, int *a, int old_k, int new_k) {
    int i;

    for (i = 0; i < n; ++i) {
        if (a[i] == old_k) {
            a[i] = new_k;
        }
    }
}
```

## 说明

这道题适合验证“条件式原地更新”模式：

- 不是每轮都写
- 更新逻辑取决于当前元素是否命中
