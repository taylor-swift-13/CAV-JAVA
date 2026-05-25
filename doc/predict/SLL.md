# Singly Linked List Predicates

## 头文件

按需求分三类：

```c
#include "sll_def.h"
```

```c
#include "sll_shape_def.h"
```

```c
#include "poly_sll_def.h"
```

## `sll_def.h`: 带元素内容的单链表

| 谓词 | 作用 | 何时用 |
| --- | --- | --- |
| `sll(p, l)` | 从 `p` 出发的完整单链表，元素序列是 `l` | 反转、压栈、弹栈、遍历 |
| `sllseg(p, q, l)` | 从 `p` 到 `q` 的前向段，内容是 `l` | 遍历前缀、尾插前的已处理部分 |
| `sllbseg(p, q, l)` | 另一种段谓词 | 某些尾部或盒式分解场景 |

最常用的是 `sll` 和 `sllseg`。

### 直接可抄的规格

```c
/*@ With l
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
```

代表例子：

- `QualifiedCProgramming/QCP_examples/poly_sll.c`

### 最常见的不变量形状

```c
/*@ Inv
    exists l1 l2,
      l == app(rev(l1), l2) &&
      sll(w, l1) *
      sll(v, l2)
*/
```

这个模板适合反转、拆分、双指针重排。

### `sll` 的打开方向

根据 `sll.strategies`，`sll(p, cons(x, l))` 常可打开成：

```c
p != 0 &&
data_at(field_addr(p, list, data), I32, x) *
data_at(field_addr(p, list, next), PTR(struct list), y) *
sll(y, l)
```

而 `sll(p, nil)` 对应空指针情形。仓库里更常直接写简洁版：

```c
p != 0 && p->data == x && p->next == y && sll(y, l)
```

## `sll_shape_def.h`: 只关心形状

| 谓词 | 作用 |
| --- | --- |
| `listrep(p)` | 从 `p` 出发的完整链表形状 |
| `lseg(x, y)` | 从 `x` 到 `y` 的链表段 |
| `listboxseg(x, y)` | 盒式段谓词 |

如果题目只关心“它还是一条合法链表”，不关心元素值，优先用这组，自动化通常更稳。

代表例子：

- `QualifiedCProgramming/QCP_examples/sll_auto.c`

里面最常抄的循环不变量是：

```c
/*@ Inv listrep(w) * listrep(v) */
```

或者：

```c
/*@ Inv lseg(x@pre, p) * listrep(p) */
```

## `poly_sll_def.h`: 多态单链表

| 谓词 | 作用 |
| --- | --- |
| `sll(storeA, p, l)` | 以 `storeA` 解释节点 `data` 域，内容表为 `l` |
| `sllseg(storeA, p, q, l)` | 多态链表段 |
| `sll_para(storeA)` | `storeA` 的良构性条件 |

这类链表适合节点里存 `void *data` 的情况。`storeA` 是“如何解释 data 域”的参数化断言。

代表例子：

- `QualifiedCProgramming/QCP_examples/poly_sll.c`

## 什么时候选哪一组

| 目标 | 优先选择 |
| --- | --- |
| 要保留元素序列语义 | `sll` |
| 只关心形状是否合法 | `listrep` |
| 节点 `data` 是指针或泛型对象 | `poly_sll` |
| 遍历一半，另一半还没处理 | `sllseg` 或 `lseg` |

## 现成例子

- `sll` 风格: `QualifiedCProgramming/QCP_examples/sll_queue.c`
- `listrep/lseg` 风格: `QualifiedCProgramming/QCP_examples/sll_auto.c`
- 多态风格: `QualifiedCProgramming/QCP_examples/poly_sll.c`
