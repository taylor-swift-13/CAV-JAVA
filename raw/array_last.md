# Array Last Element

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回最后一个元素。

约定：

- `n >= 1`
- 数组长度恰好是 `n`
- 函数不修改数组

## 正确代码

```c
int array_last(int n, int *a) {
    return a[n - 1];
}
```

## 说明

这道题是基础数组索引题：

- 没有循环
- 没有分支
- contract 需要保证 `n >= 1`
