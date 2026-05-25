# Array Predicates

## 头文件

```c
#include "int_array_def.h"
```

这个头文件同时带来三组数组谓词：

- `IntArray::*`：`int *`
- `UIntArray::*`：`unsigned int *`
- `PtrArray::*`：指针数组

## `IntArray` 常用谓词

| 谓词 | 作用 | 何时用 |
| --- | --- | --- |
| `IntArray::full(a, n, l)` | 整个长度为 `n` 的数组 `a`，其抽象内容为 `l` | 读整个数组、写后仍保持抽象内容 |
| `IntArray::seg(a, lo, hi, l)` | 子区间 `[lo, hi)` 的数组段 | 归并、双指针、前后缀 |
| `IntArray::missing_i(a, i, lo, hi, l)` | 区间 `[lo, hi)` 已打开第 `i` 个槽位 | 读写单个元素 |
| `IntArray::full_shape(a, n)` | 只知道有完整数组，不关心值 | 形状题、自动证明题 |
| `IntArray::seg_shape(a, lo, hi)` | 只知道某段存在 | 复制、拼接、写入 |
| `IntArray::undef_full(a, n)` | 整段已分配但未初始化 | `memset`、新数组填充 |
| `IntArray::undef_seg(a, lo, hi)` | 未初始化的子段 | 循环逐步写数组 |

辅助函数：

- `sum(l)`
- `sublist(lo, hi, l)`
- `Znth(i, l, default)`
- `replace_Znth(i, v, l)`
- `zeros(n)`

## `UIntArray` 常用谓词

`UIntArray::*` 用法和 `IntArray::*` 完全平行，区别只在底层单元是 `unsigned int`。如果程序里是 `unsigned int *`，优先用它，不要混写成 `IntArray::*`。

## `PtrArray` 常用谓词

`PtrArray::*` 用法也平行：

- `PtrArray::full`
- `PtrArray::seg`
- `PtrArray::missing_i`
- `PtrArray::full_shape`
- `PtrArray::undef_full`

适合验证“数组里存的是地址”的程序。当前 `QCP_examples` 里直接样例不多，但头文件和 strategies 已经具备。

## 最常抄的三种模板

### 1. 只读整数组

```c
/*@ With l
    Require 0 <= n && IntArray::full(a, n, l)
    Ensure IntArray::full(a, n, l)
*/
```

代表例子：

- `QualifiedCProgramming/QCP_examples/sum.c`

### 2. 前缀已处理、后缀未处理

```c
/*@ Inv
    0 <= i && i <= n@pre &&
    IntArray::full(a, n@pre, app(done_prefix, rest_suffix))
*/
```

或者 shape-only 版本：

```c
/*@ Inv
    0 <= i && i <= n@pre &&
    IntArray::seg_shape(dest@pre, 0, i) *
    IntArray::undef_seg(dest@pre, i, n@pre)
*/
```

代表例子：

- `QualifiedCProgramming/QCP_examples/array_auto.c`
- `QualifiedCProgramming/QCP_examples/chars.c`

### 3. 打开单个单元进行读写

```c
/*@ IntArray::full(a, n, l)
    which implies
    data_at(a + (i * sizeof(int)), int, l[i]) *
    IntArray::missing_i(a, i, 0, n, l)
*/
```

写回后通常折回两种形式之一：

- 值没变：折回 `IntArray::full(a, n, l)`
- 值变了：折回 `IntArray::full(a, n, replace_Znth(i, v, l))`

直接参考：

- `QualifiedCProgramming/QCP_examples/sum.c`

## `seg` 什么时候优先于 `full`

以下场景优先用 `seg`：

- 只处理子数组 `[l, r]`
- 归并排序或分治
- 一个数组被逻辑上切成多段
- 想把“已完成部分”和“待完成部分”明确分开

代表例子：

- `QualifiedCProgramming/QCP_examples/int_array_merge_rel.c`

里面典型写法是：

```c
IntArray::seg(arr, p, i, l_done) *
IntArray::seg(arr, i, q + 1, l_rest)
```

## `shape` 版本什么时候更好

如果题目只关心：

- 不越界
- 写满整个目标数组
- 输入输出数组都仍然是合法数组

而不关心精确内容，优先用：

- `IntArray::full_shape`
- `UIntArray::full_shape`
- `IntArray::seg_shape`
- `UIntArray::seg_shape`

这样 annotation 更短，自动化通常也更好。代表例子：

- `QualifiedCProgramming/QCP_examples/array_auto.c`

## 常见坑

- `full` 需要内容表 `l` 和长度对齐，循环不变量里经常要补 `n@pre == Zlength(l)`。
- 打开单元时，`data_at` 地址要写成 `a + (i * sizeof(int))`。
- 更新数组时，不要忘了后置条件里的抽象内容也要同步更新。
- `UIntArray::*` 和 `IntArray::*` 不要混用。