# Common Predicates And Annotation Syntax

## 最常用的 include

```c
#include "verification_stdlib.h"
#include "verification_list.h"
```

如果要用某类数据结构，再额外 include 对应的 `*_def.h`。

## 通用断言元素

| 写法 | 作用 | 典型场景 |
| --- | --- | --- |
| `emp` | 空堆，没有额外内存资源 | `malloc` 前置条件、释放后后置条件 |
| `data_at(addr, T, v)` | 地址 `addr` 处有一个类型为 `T` 的已初始化值 `v` | 打开单个数组单元、字段、局部变量 |
| `undef_data_at(addr)` | 地址 `addr` 已分配但未初始化，不能读取 | 局部变量声明后、`malloc` 后尚未赋值 |
| `P * Q` | 分离合取，表示两块互不重叠的资源同时成立 | 链表和数组段拼接 |
| `P && Q` | 纯逻辑条件合取 | 下标范围、数学关系 |
| `exists x, ...` | 存在量化 | 打开数据结构后暴露内部值 |
| `With l ...` | 给函数规格引入逻辑变量 | 抽象数组内容、抽象树内容 |
| `x@pre` | 函数入口处的程序变量值 | 不变量里固定初始参数 |
| `__return` | 函数返回值 | 后置条件 |

## 手工 annotation 的三个关键标记

| 写法 | 作用 |
| --- | --- |
| `Require ...` | 前置条件 |
| `Ensure ...` | 后置条件 |
| `Inv ...` | 循环不变量 |

常见模板：

```c
/*@ With l
    Require P(l)
    Ensure Q(__return, l)
*/
```

```c
/*@ Inv
    0 <= i && i <= n@pre && ...
*/
```

## `Assert` 和 `which implies`

这两个写法很实用。

### `Assert`

用于在程序点上强行切换到你想证明的中间状态，适合：

- while 后想固定退出条件
- 调函数前想把资源整理成目标规格
- case split 后想把多个事实收束起来

示例风格见：

- `QualifiedCProgramming/QCP_examples/int_array_merge_rel.c`
- `QualifiedCProgramming/QCP_examples/eval.c`

### `which implies`

用于把一个抽象谓词手工打开成更适合当前语句的形状，或者把局部资源重新折回去。典型是：

- `IntArray::full` 打开成某个 `data_at` 加 `IntArray::missing_i`
- `store_expr` 打开成 `store_expr_aux`
- `store_queue` 打开成底层链表或分段链表

示例：

```c
/*@ IntArray::full(a, n, l)
    which implies
    data_at(a + (i * sizeof(int)), int, l[i]) *
    IntArray::missing_i(a, i, 0, n, l)
*/
```

## 列表逻辑运算

来自 `verification_list.h`：

| 名字 | 作用 |
| --- | --- |
| `nil` | 空表 |
| `cons(x, l)` | 头插 |
| `app(l1, l2)` | 拼接 |
| `rev(l)` | 反转 |
| `Zlength(l)` | 长度 |

数组和链表题几乎都会用到这些运算。

## 写 annotation 的默认顺序

1. 先写纯条件，如范围、长度、`x@pre` 不变式。
2. 再写资源断言，如 `IntArray::full(...)`、`sll(...)`、`store_tree(...)`。
3. 循环里优先采用“已处理前缀 + 未处理后缀”的分解。
4. 读写单个位置时，先用 `which implies` 打开成 `data_at`，操作后再折回。

## 现成语法参考

- 教程: `QualifiedCProgramming/tutorial/T3-assertion-and-invariant.md`
- 教程: `QualifiedCProgramming/tutorial/T4-symbolic-execution.md`
- 数组例子: `QualifiedCProgramming/QCP_examples/sum.c`
- 链表例子: `QualifiedCProgramming/QCP_examples/sll_auto.c`
