# Expression Tree Predicates

## 头文件

```c
#include "eval_def.h"
```

## 常用谓词和函数

| 名字 | 作用 | 何时用 |
| --- | --- | --- |
| `store_expr(e, e0)` | 指针 `e` 指向的 AST 抽象值是 `e0` | 表达式求值、编译、解释器 |
| `store_expr_aux(e, tag, e0)` | 打开 tag 后的细化表示 | `switch (e->t)` 之后 |
| `safe_eval(e0, l)` | 表达式在环境 `l` 上安全可求值 | 除零、越界等前提 |
| `expr_eval(e0, l)` | 语义求值结果 | 后置条件 |
| `store_int_array(ptr, n, l)` | 表达式库里用到的整数数组表示 | 变量表等 |

构造器：

- `EConst`
- `EVar`
- `EBinop`
- `EUnop`

## 最常抄的规格

```c
/*@ With (e0: expr) (l: list Z)
    Require safe_eval(e0, l) &&
            store_expr(e, e0) *
            IntArray::full(var_value, 100, l)
    Ensure __return == expr_eval(e0, l) &&
           store_expr(e, e0) *
           IntArray::full(var_value, 100, l)
*/
```

代表例子：

- `QualifiedCProgramming/QCP_examples/eval.c`

## `store_expr` 的典型展开

进入 `switch (e->t)` 前，常先写：

```c
/*@ store_expr(e, e0)
    which implies
    store_expr_aux(e, e->t, e0)
*/
```

然后每个 case 再细分。

### `T_CONST`

```c
/*@ e->t == T_CONST && store_expr_aux(e, e->t, e0)
    which implies
    exists n,
      e0 == EConst(n) &&
      e->d.CONST.value == n
*/
```

### `T_VAR`

```c
/*@ e->t == T_VAR &&
    safe_eval(e0, l) &&
    store_expr_aux(e, e->t, e0) *
    IntArray::full(var_value, 100, l)
    which implies
    exists n,
      0 <= n && n < 100 &&
      e0 == EVar(n) &&
      e->d.VAR.name == n
*/
```

### `T_BINOP`

```c
/*@ e->t == T_BINOP && store_expr_aux(e, e->t, e0)
    which implies
    exists e1 e2 op,
      e0 == EBinop(op, e1, e2) &&
      e->d.BINOP.op == BinOpID(op) &&
      store_expr(e->d.BINOP.left, e1) *
      store_expr(e->d.BINOP.right, e2)
*/
```

## 什么时候用这组谓词

- 解释器、求值器
- AST 递归函数
- 语法树结构不变，但计算结果变化
- 需要把 C 结构体树和 Coq 抽象语法树对齐

## 常见坑

- `store_expr` 往往要先转成 `store_expr_aux` 才方便做 `switch`。
- 变量求值通常同时需要 `IntArray::full(var_value, 100, l)`。
- `safe_eval` 是纯前提，表达“这棵树在当前环境下不会出语义错误”。它不是堆资源。
