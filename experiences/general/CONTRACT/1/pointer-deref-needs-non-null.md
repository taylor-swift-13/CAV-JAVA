# 直接 deref 指针入参时，contract 要保证 VC 整体可证（2026-05-28）

QCP 的 `symexec` **不会**从 shape predicate 自动抽指针非空送到每个 VC 的 LHS。`sll p (cons x l)` 的 cons 分支虽然带 `“ x <> NULL ”`，但展开后这条纯条件只在 `partial_solve_wit_1` 内部短暂出现、被丢弃，**不会传到 `return_wit_1` 的 LHS**。把字段 cells 折回 `sll p (cons x l)` 时缺 `p <> NULL`，`entailer!` 收不掉，定理不可证。

适用场景：函数体**直接 deref 指针入参**（`p->field`、`*p`、`p[i]`）且**没有任何控制流 guard**（没有 `if (p)` / `while (p)` 让 symexec 自动把 `p != 0` 加到分支的路径条件）。

### 解决思路：让 contract 设计跟 symexec 实际能给的 VC 形状对齐

核心不是「必须加 `p != 0`」，而是「**保证生成的所有 VC 都可证**」。常见两种走法：

**A. 让前条件显式带 `p != 0`**（最直接）：

```c
int sll_head(struct list *p)
/*@ Require p != 0 && sll(p, cons(x, l))
    Ensure  __return == x && sll(p@pre, cons(x, l))
*/
{ return p->data; }
```

`symexec` 把 `p_pre <> 0` 塞进每个 VC 的 LHS，`entailer!` 自动收。

**B. 让后条件自身能承载 partial 行为**（保留前条件简洁）：

如果不想冗余写 `p != 0`，可以把后条件改成**对 `p` 是否为 0 分类讨论**，让 partial（p=0 时不可达）这件事在后条件层面被吸收。例如：

```c
/*@ Require sll(p, cons(x, l))
    Ensure (p@pre == 0 -> False) &&
           (p@pre <> 0 -> __return == x && sll(p@pre, cons(x, l)))
*/
```

或把折回 sll 这一步从后条件里去掉、留 unfolded 形式（这样 return_wit 退化成纯 cancel）：

```c
/*@ Require sll(p, cons(x, l))
    Ensure  __return == x && (... unfolded cells + sll y l ...)
*/
```

任何一种走法的检验标准都是同一个：**所有 wit 的 LHS 必须能推出 RHS 需要的全部纯条件**。

### 参考 QCP demos 的实际写法

`QualifiedCProgramming/QCP_examples/QCP_demos_LLM/sll.c` 里的 `length` / `reverse` / `append` 全部走「控制流 guard + invariant 显式 `p != 0`」路径，因为它们都是循环结构、guard 是天然存在的；前条件只写 `sll(p, l)` 是因为非空靠 `while (p)` / `if (p == 0)` 在体内重新塑形。**没有任何 demo 依赖「`sll(p, cons(...))` 自动蕴含非空」**——这就是 QCP 的设计约定。

### 反例（这次踩坑）

`input/sll_head.c` 早期写法：`Require sll(p, cons(x, l))` + 直接 `return p->data;`。`coqc` 在 `proof_manual.v` 报「remaining open goal: `(p_pre <> NULL)`」。`sep_apply valid_store_int` 抽出的 `isvalidptr_int (&p.data)` 展开是 `addr >= 0 ∧ aligned_4 addr ∧ addr+3 ≤ max`——0 满足全部三条，所以从 mapsto 推不出 `<> 0`。改 contract（加 `p != 0`，或调整后条件结构）才是对的。

不要把这类问题留给 Verify 阶段尝试用证明 tactic 绕过；这是 Contract 层的固定义务。
