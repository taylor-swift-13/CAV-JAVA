# Array Intersection Count Sorted

## 问题描述

实现一个函数，统计两个有序数组的多重集合交集大小。

约定：
- `n >= 0`，`m >= 0`。
- `a` 指向长度至少为 `n` 的整数数组，`b` 指向长度至少为 `m` 的整数数组。
- 两个数组都按非降序排列。
- 如果一个值在两个数组中都出现多次，则按可以配对的次数计数。

## 正确代码

```c
int array_intersection_count_sorted(int n, int *a, int m, int *b) {
    int i = 0;
    int j = 0;
    int count = 0;
    while (i < n && j < m) {
        if (a[i] == b[j]) {
            count++;
            i++;
            j++;
        } else if (a[i] < b[j]) {
            i++;
        } else {
            j++;
        }
    }
    return count;
}
```

## 说明

这段代码使用两个指针扫描两个有序数组。元素相等时形成一次配对；较小的一侧不可能再和当前较大元素配对，因此向前移动。
