# Array Reverse In Place

## 问题描述

实现一个函数，原地反转一个整数数组。

约定：
- `n` 表示数组长度，`n >= 0`。
- `a` 指向长度至少为 `n` 的整数数组。
- 函数不分配新数组，只通过交换元素修改 `a`。
- 返回后，`a[i]` 等于原数组中的 `a[n - 1 - i]`。

## 正确代码

```c
void array_reverse_in_place(int n, int *a) {
    int left = 0;
    int right = n - 1;
    while (left < right) {
        int tmp = a[left];
        a[left] = a[right];
        a[right] = tmp;
        left++;
        right--;
    }
}
```

## 说明

这段代码使用双指针从数组两端向中间移动。每一轮交换一对对称位置的元素，因此循环结束后整个数组被原地反转。
