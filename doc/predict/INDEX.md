# Predicate Index

这组文档整理的是 `QualifiedCProgramming/QCP_examples` 里已经定义好的、可以直接写进 annotation 的谓词和辅助函数。目标不是重复 Coq 定义，而是告诉模型或人工写注释时：

- 该 include 哪个 `*_def.h`
- 该选哪个谓词
- 常见的 unfold / fold 方向是什么
- 仓库里哪里有现成例子可以直接抄

## 使用顺序

1. 先确定数据类型和头文件。
2. 优先选“整段拥有”谓词，比如 `IntArray::full`、`sll`、`store_queue`、`store_tree`。
3. 需要循环拆开时，再改成 `seg`、`missing_i`、`lseg`、`store_ptb` 这类局部谓词。
4. 如果题目只关心内存形状，不关心元素值，优先用 `*_shape` 或 `undef_*`。
5. 如果仓库里已有几乎同构的例子，直接参考对应 `.c` 的写法。

## 文档列表

- [COMMON.md](COMMON.md): 通用断言语言、`data_at`、`undef_data_at`、`Inv`、`which implies`
- [ARRAY.md](ARRAY.md): `IntArray`、`UIntArray`、`PtrArray`
- [STRING.md](STRING.md): `CharArray` 和 C 风格字符串
- [SLL.md](SLL.md): 单链表、形状链表、多态单链表
- [DLL.md](DLL.md): 双链表形状与双链表段
- [QUEUE.md](QUEUE.md): 三种 `store_queue`
- [TREE.md](TREE.md): BST、带父指针 BST、AVL
- [EXPR.md](EXPR.md): 表达式树 `store_expr`

## 快速选型

| 场景 | 优先谓词 |
| --- | --- |
| 读整个整数数组 | `IntArray::full(a, n, l)` |
| 写一个未初始化数组 | `IntArray::undef_full(a, n)` |
| 只关心数组形状 | `IntArray::full_shape(a, n)` / `UIntArray::full_shape(a, n)` |
| 处理数组前缀或子区间 | `IntArray::seg(...)` / `UIntArray::seg(...)` |
| 打开单个数组元素 | `IntArray::missing_i(...) * data_at(...)` |
| C 字符串 | `CharArray::full(s, n + 1, app(l, cons(0, nil)))` |
| 整个单链表并保留元素序列 | `sll(p, l)` |
| 只关心单链表形状 | `listrep(p)` |
| 单链表前缀加剩余表 | `lseg(x, p) * listrep(p)` 或 `sllseg(x, p, l)` |
| 双链表形状 | `dlistrep_shape(p, prev)` |
| 队列抽象语义 | `store_queue(q, l)` |
| BST 抽象 map 语义 | `Bst::store_map(root, m)` |
| BST 具体树结构 | `store_tree(root, tr)` |
| AVL 局部旋转 | `single_tree_node(...)` + `store_tree_shape(...)` |
| 表达式 AST | `store_expr(e, e0)` |

## 直接参考的代表性例子

- 数组: `QualifiedCProgramming/QCP_examples/sum.c`
- 数组 shape: `QualifiedCProgramming/QCP_examples/array_auto.c`
- 字符串: `QualifiedCProgramming/QCP_examples/chars.c`
- 字符串加数组: `QualifiedCProgramming/QCP_examples/kmp_rel.c`
- 单链表: `QualifiedCProgramming/QCP_examples/sll_auto.c`
- 多态单链表: `QualifiedCProgramming/QCP_examples/poly_sll.c`
- 双链表: `QualifiedCProgramming/QCP_examples/dll_auto.c`
- 队列: `QualifiedCProgramming/QCP_examples/sll_queue.c`
- BST: `QualifiedCProgramming/QCP_examples/bst_insert.c`
- AVL: `QualifiedCProgramming/QCP_examples/avl_insert.c`
- 表达式树: `QualifiedCProgramming/QCP_examples/eval.c`
