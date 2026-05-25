# Doubly Linked List Predicates

## 头文件

```c
#include "dll_shape_def.h"
```

如果是双链表队列，还会用到：

```c
#include "dll_queue_def.h"
```

## `dll_shape_def.h`

| 谓词 | 作用 | 何时用 |
| --- | --- | --- |
| `dlistrep_shape(p, prev)` | 一条完整双链表，头节点前驱是 `prev` | 反转、遍历、拼接 |
| `dllseg_shape(h, h_prev, t_prev, t)` | 双链表段 | 前缀 / 后缀分解 |

这组谓词是 shape-only 的，不直接记录值序列，适合：

- 只关心 `next` / `prev` 链接是否正确
- 自动证明优先
- 结构操作多、值语义弱

## 最常抄的模板

### 1. 完整双链表

```c
/*@ Require dlistrep_shape(x, 0)
    Ensure dlistrep_shape(__return, 0)
*/
```

代表例子：

- `QualifiedCProgramming/QCP_examples/dll_auto.c`

### 2. 已处理段加剩余段

```c
/*@ Inv
    exists p_prev,
      dllseg_shape(head, 0, p_prev, p) *
      dlistrep_shape(p, p_prev)
*/
```

这种形状在前向遍历和复制时都很常见。

### 3. 前后两部分相互作为前驱信息

反转时常写成：

```c
/*@ Inv
    dlistrep_shape(w, v) *
    dlistrep_shape(v, w)
*/
```

代表例子：

- `QualifiedCProgramming/QCP_examples/dll_auto.c`

## `dll_queue_def.h` 里的 `dllseg`

双链表队列除了 `store_queue` 外，还定义了：

```c
dllseg(head, head_prev, tail_next, tail, l)
```

它记录一段带内容序列 `l` 的双链表段，适合队列内部展开。最常见展开写法是：

```c
store_queue(q, l)
which implies
dllseg(q->head, 0, 0, q->tail, l)
```

代表例子：

- `QualifiedCProgramming/QCP_examples/dll_queue.c`

## 常见坑

- `dlistrep_shape` 的第二个参数不是长度，而是头节点逻辑前驱。
- 双链表操作后，`next` 和 `prev` 两边都要维护。
- 如果题目只做队列操作，优先用 `store_queue`，不要一开始就手写 `dllseg`。
