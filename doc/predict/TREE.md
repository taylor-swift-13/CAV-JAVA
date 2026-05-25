# Tree Predicates

## 头文件

```c
#include "bst_def.h"
```

```c
#include "bst_fp_def.h"
```

```c
#include "avl_def.h"
```

## BST: `bst_def.h`

| 谓词 / 函数 | 作用 | 何时用 |
| --- | --- | --- |
| `Bst::store_map(root, m)` | 抽象成有限映射 `m` | 写高层规格 |
| `store_tree(root, tr)` | 具体树结构 + 抽象树值 `tr` | 写函数体低层规格 |
| `store_ptb(b, b0, pt)` | 迭代式 zipper / partial tree | while 循环沿路径向下走 |
| `store_pt(b, b0, pt)` | 另一种 partial tree 资源 | 局部路径推理 |
| `tree_insert` / `map_insert` | 树插入与 map 插入 | 对齐高低层规格 |
| `tree_delete` / `map_delete` | 树删除与 map 删除 | 对齐高低层规格 |
| `combine_tree(pt, tr)` | 路径和子树重新拼回整树 | 循环不变量里最常见 |

### 最推荐的写法

高层规格先写：

```c
/*@ With m
    Require Bst::store_map(*b, m)
    Ensure Bst::store_map(*b, map_insert(x, value, m))
*/
```

低层实现再写：

```c
/*@ With tr
    Require store_tree(*b, tr)
    Ensure store_tree(*b, tree_insert(x, value, tr))
*/
```

代表例子：

- `QualifiedCProgramming/QCP_examples/bst_insert.c`

### while 向下搜索时的标准不变量

```c
/*@ Inv
      exists pt0 tr0,
        combine_tree(pt0, tree_insert(x@pre, value@pre, tr0)) ==
          tree_insert(x@pre, value@pre, tr) &&
        store_ptb(b, b@pre, pt0) *
        store_tree(*b, tr0)
*/
```

这是 BST 迭代插入里最值得直接复用的模板。

## 带父指针 BST: `bst_fp_def.h`

和普通 BST 最大区别是：

- `store_tree(root, fa, tr)` 多了父指针参数
- `store_ptb(b, b0, fa, fa0, pt)` 等 partial tree 谓词也多了父指针上下文

适用文件：

- `QualifiedCProgramming/QCP_examples/bst_fp_insert.c`
- `QualifiedCProgramming/QCP_examples/bst_fp_delete.c`

最常见低层规格：

```c
/*@ With tr
    Require store_tree(*b, 0, tr)
    Ensure store_tree(*b, 0, tree_insert(x, value, tr))
*/
```

如果进入左右子树，需要同步更新 `fa`。

## AVL: `avl_def.h`

| 谓词 | 作用 | 何时用 |
| --- | --- | --- |
| `store_tree(root, tr)` | 完整 AVL 抽象树 | 全局语义 |
| `store_tree_shape(root)` | 只关心 AVL 节点形状 | 插入和旋转的主规格 |
| `store_non_empty_tree(root)` | 非空树形状 | 旋转前提 |
| `single_tree_node(root, k, v, h, l, r)` | 单个根节点资源 | 局部旋转、局部展开 |

适用文件：

- `QualifiedCProgramming/QCP_examples/avl_insert.c`

### 旋转时的标准局部规格

右旋常写成：

```c
/*@ With l r k v h
    Require root != 0 &&
            single_tree_node(root, k, v, h, l, r) *
            store_non_empty_tree(l) *
            store_tree_shape(r)
    Ensure __return == l &&
           store_non_empty_tree(l)
*/
```

这类规格的思路是：

- 先把根节点单独拿出来
- 左右子树分别用 `store_non_empty_tree` / `store_tree_shape`
- 旋转后只保证局部 shape 正确

## 选择建议

| 目标 | 优先谓词 |
| --- | --- |
| 只想表达插入/删除的抽象行为 | `Bst::store_map` |
| 要写 BST 函数体证明 | `store_tree` |
| while 沿搜索路径下钻 | `store_ptb` |
| 树带父指针 | `bst_fp_def.h` 的 `store_tree` |
| AVL 局部旋转 | `single_tree_node` + `store_tree_shape` |

## 常见坑

- `Bst::store_map` 适合高层规格，不够细，不适合直接驱动函数体的每一步。
- 迭代 BST 证明里，`combine_tree` 和 `store_ptb` 基本是成对出现的。
- AVL 题通常先证明 shape，不必一开始就把平衡性质编码得太重。
