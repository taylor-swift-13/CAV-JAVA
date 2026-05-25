# Queue Predicates

这个仓库里有三种队列抽象，都叫 `store_queue`，但来源头文件不同，底层表示也不同。不要混用。

## 头文件

```c
#include "sll_queue_def.h"
```

```c
#include "dll_queue_def.h"
```

```c
#include "functional_queue_def.h"
```

## 共同的高层规格

三种实现都可以先写成：

```c
/*@ With l
    Require store_queue(q, l)
    Ensure store_queue(q, app(l, cons(x, nil)))
*/
```

或：

```c
/*@ With x l
    Require store_queue(q, cons(x, l))
    Ensure __return == x && store_queue(q, l)
*/
```

也就是把队列当成抽象序列 `l`。

## `sll_queue_def.h`

适用文件：

- `QualifiedCProgramming/QCP_examples/sll_queue.c`

高层谓词：

- `store_queue(q, l)`

常见底层展开：

```c
/*@ store_queue(q, l)
    which implies
    exists u v,
      q->tail != 0 &&
      q->tail->data == u &&
      q->tail->next == v &&
      sllseg(q->head, q->tail, l)
*/
```

适合：

- 尾指针指向“哨兵尾节点”
- 入队在尾部写值并延长一格

## `dll_queue_def.h`

适用文件：

- `QualifiedCProgramming/QCP_examples/dll_queue.c`

高层谓词：

- `store_queue(q, l)`

常见底层展开：

```c
/*@ store_queue(q, l)
    which implies
    dllseg(q->head, 0, 0, q->tail, l)
*/
```

出队时常进一步打开成：

```c
q->head->prev == 0 &&
q->head->data == x &&
dllseg(q->head->next, 0, q->head, q->tail, l)
```

适合：

- 需要维护 `prev`
- 需要 O(1) 双端结构推理

## `functional_queue_def.h`

适用文件：

- `QualifiedCProgramming/QCP_examples/functional_queue.c`

高层谓词：

- `store_queue(q, l)`

最关键的展开是：

```c
/*@ store_queue(q, l)
    which implies
    exists l1 l2,
      l == app(l1, rev(l2)) &&
      sll(q->l1, l1) *
      sll(q->l2, l2)
*/
```

这表示函数式队列用两条链表表示：

- `l1` 是前半队列
- `l2` 是反向累积的后半队列

适合：

- 入队只往 `l2` 压栈
- 出队时若 `l1` 为空，就把 `l2` 反转搬过去

## 选择建议

| 题目类型 | 优先谓词 |
| --- | --- |
| 单链表哨兵队列 | `sll_queue_def.h` 的 `store_queue` |
| 双链表队列 | `dll_queue_def.h` 的 `store_queue` |
| 双栈函数式队列 | `functional_queue_def.h` 的 `store_queue` |

## 常见坑

- 三个头文件里的 `store_queue` 同名，但语义不同。
- 写 annotation 时，先用抽象 `store_queue`，只有在具体语句前才 `which implies` 展开。
- `functional_queue` 的抽象序列是 `app(l1, rev(l2))`，不是 `app(l1, l2)`。
