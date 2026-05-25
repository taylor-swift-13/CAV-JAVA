# Proof Experience

本文件只记录 `coq/generated/<name>_proof_manual.v` 的手工证明经验。

常见入口：

- proof 阶段范围和退出条件：看 1
- 开始证明前该读什么：看 2
- 第一轮最短 proof 骨架：看 3
- 编译失败要看完整 proof state：看 5
- 卡住时检索例子：看 6
- witness 太复杂，需要 helper lemma：看 7
- `Cannot find witness`：看 8、19
- 多个相似 list 导致 helper 参数实例化错：看 20
- merge / two-pointer：看 21
- QCP assertion-level `Left` / `Right` / `Exists`：看 22
- hypothesis 编号复制错：看 23
- return witness prefix/suffix 归一化：看 24
- `replace_Znth` / nat index：看 25
- `entailer!` 后目标顺序：看 27
- insertion sort final witness：看 31、32
- 生成文件不要手改：看 34
- 复用旧 proof 前比较 VC 主体：看 35
- `split_pures` 后空间侧处理：看 36
- safeExec / refinement 目标：看 37

## 1. 证明范围

- 只记录 manual proof
- 不记录 invariant/assert/symexec
- 不记录 Coq 编译与路径问题
- 如果 `proof_manual.v` 里没有需要手工证明的 theorem，就直接跳过 manual proof 和 `proof_reasoning.md`
- 如果 `proof_manual.v` 或 `goal_check.v` 还没有编译通过，就不能退出 proof 阶段，必须继续证明
- 只有到达明确外部边界时，才允许以 `Fail` 结束 proof：具体只包括已用反例确认的 contract gap、当前 workspace 内无法排除的外部工具/环境故障、外部时间上限触发，或调用方明确要求停止；剩一个 witness、某轮 `coqc` 失败、暂时想不到 tactic、当前写法还没证通，都不算可结束理由
- 如果以 `Fail` 结束 proof，必须在 `logs/proof_reasoning.md`、`logs/issues.md`、`logs/metrics.md` 中写清楚属于哪一种边界，以及对应的具体证据；没有证据就不允许收尾

## 2. 开始前先读当前目标

- 先读 `goal.v`
- 再读 `proof_auto.v`
- 再读 `goal_check.v`
- 先确认当前 witness 的前置条件、结论和上下文变量
- 第一轮分析先写入 `logs/proof_reasoning.md`

## 3. 先做最短证明骨架

- 先试 `pre_process`
- 再试 `entailer!`
- 纯算术部分优先交给 `lia`
- 每一轮失败后，都要把新的失败点、原因判断和下一步计划追加写入 `logs/proof_reasoning.md`

## 4. 先分清卡点类型

- 算术问题
- 改写问题
- 结构展开问题
- exist / case split 问题
- 辅助引理缺失

不要一上来就重写整段证明。

## 5. 编译失败时先看完整 proof state

- 不能只看 `coqc` 的单行报错
- 应优先用 `coqtop` 进入当前定理，查看具体假设、子目标和 tactic 后状态
- 首先搞清楚当前真正缺的是什么，再决定改 proof、加 rewrite 还是补引理

## 6. 卡住时去例子库检索

- proof 卡住时，按 `doc/retrieval/INDEX.md` 检索相关例子
- 优先看顶层 `examples/`
- 如果 `examples/` 没有足够接近的例子，再扩大到整个 `QualifiedCProgramming/QCP_examples/`
- 检索后要明确写出：当前目标为什么证不出来，现有例子提供了什么可复用 proof pattern

## 7. 主 witness 不要硬顶 tactic，先抽 helper lemma

如果主 witness 同时承担下面几件事：

- 展开结构
- 改写列表/数组表达式
- 处理算术 side condition
- 证明核心语义结论

就不要继续在主 witness 里硬顶 tactic。

更稳的做法是：

- 主 witness 只负责 `Exists`、`Intros`、`subst`、`rewrite`、调用引理
- 把反复出现的 list / arithmetic / sublist / append / max-min 事实先抽成 helper lemma
- helper lemma 直接写在当前 `coq/generated/<name>_proof_manual.v`

主 witness 越短，越容易编译稳定；复杂 proof 应该沉到辅助引理里。

## 8. `Cannot find witness` 往往不是神秘错误，而是 side condition 不显式

这类报错常见于：

- `lia` 需要非空条件，但上下文里没显式写出来
- 需要长度事实，但只有隐含的 `Zlength` 关系
- `Znth` / `sublist` / `replace_Znth` 的边界条件还没固定

遇到这类错误时，先不要继续换 tactic。

优先补这些显式事实：

- 非空
- 长度
- 边界
- 索引范围
- 当前分支下的等式关系

经验上，很多 `Cannot find witness` 在补完这类中间 `assert` 后就会消失。

## 9. Coq 脚本尽量写保守，不要过度依赖自动化和自动命名

更稳的写法是：

- 少用复杂的 intro-pattern
- 少依赖自动命名的 `IH`
- 中间事实用 `assert` 明确命名
- 重写后把关键索引和等式显式化简

不稳的写法通常是：

- 一步塞太多 pattern
- 指望 `lia` 自动猜出所有边界
- 依赖当前 Coq 版本恰好给出的 `IH` 名字或简化顺序

保守脚本虽然稍长，但在不同 Coq 版本和不同 proof state 下更稳定。

## 10. `entailer!` 收不掉时先整理上下文

- 补 `Intros`
- 补 `subst`
- 补 `rewrite`
- 分开处理 separation logic 部分和纯命题部分

## 11. 失败记录必须写首个稳定错误

- 记录文件
- 记录行号
- 记录原始错误文本
- 记录为什么这个错误会出现

## 12. 不允许绕过证明

- 不允许 `Admitted.`
- 不允许新增 `Axiom`

## 13. 改结构后必须重新 symbolic

- 改了注释
- 改了题目专用 `.v`
- 改了证明结构

都必须重新对齐 witness。

## 14. `proof_auto.v` 已经定义的 lemma，不要在 `proof_manual.v` 里重复定义

- 开始写 manual proof 前，先看一眼 `proof_auto.v`
- 如果某个 `proof_of_<name>_*` 已经在 `proof_auto.v` 里给出，就不要在 `proof_manual.v` 里再写同名 lemma
- 否则 `goal_check.v` 里同时 `Include proof_auto` 和 `Include proof_manual` 时会报重复 label

## 15. max/min 扫描题的 helper lemma 值得模板化

对 max/min 扫描类题目，反复会用到这些 lemma：

- 前缀中任意元素都不超过当前 prefix max
- 如果所有元素都不超过某个上界，则 prefix max 也不超过这个上界
- 在列表尾部追加一个元素后，max/min 的单调性
- 追加元素不改变当前 max/min 的条件

这类题的主 witness 通常不难，难点在这些纯 list helper lemma。

所以更稳的策略是：

- 尽早把它们沉淀成局部模板
- 主 witness 只做“把循环状态翻译成 prefix 语义，再调用 lemma”

不要每道 max/min 扫描题都从零在主 witness 里手搓同一套推理。

## 16. 如果 return witness 同时出现 `x` 和 `x_pre`，先检查 annotation 是否保留了 `x == x@pre`

典型现象：

- `return_wit` 看起来只差把当前参数名改回 `*_pre`
- proof 里缺的不是 list / arithmetic，而是“这个标量参数从头到尾没变”

处理顺序：

1. 先看 loop invariant 和 loop-exit assertion 是否显式保留了 `x == x@pre`
2. 如果没有，回 annotation 层补这个不变关系
3. 清理 generated 文件并重新跑 `symexec`

不要在 `proof_manual.v` 里硬证一个 annotation 本该直接保留的参数恒等关系。

## 17. 字符串/数组复制题如果只知道“当前位置读到 0”，先检查 contract 是否排除了中间 0

典型现象：

- `return_wit` 最后只剩：
  - `replace_Znth i 0 (l1 ++ d1) = l ++ [0]`
  - 或等价的 `CharArray.full ...` 目标
- 已知条件只有：
  - 前缀 `l1` 与 `l` 在 `< i` 上相等
  - `Znth i (l ++ [0]) = 0`
  - 长度关系

这时不要默认继续堆 tactic。

先判断当前 contract 是否真的能推出：

- `i = n`
- 或者 `l` 在 `0 <= k < n` 上都非零

如果都没有，那么 return witness 往往不是 proof 技巧问题，而是 specification 本身没有排除中间 `0`，导致“在第一个 `0` 处停止复制”不足以推出“整个目标数组等于 `l ++ [0]`”。

处理顺序：

1. 先用 `coqtop` 看清剩余目标是否已经退化成纯 list equality / `CharArray.full` equality
2. 如果是，就检查 precondition / ghost predicate 是否提供“唯一终止符”或“前缀元素非零”信息
3. 如果没有，优先记录为 contract gap，不要在 manual proof 里盲目硬证

## 18. 字符串扫描类 return witness 常见的真正桥接点是先证 `i = n`

对 `string_copy`、`strlen` 这类题，`return_wit` 最后看起来常常像：

- `replace_Znth i 0 (...) = l ++ [0]`
- 或等价的 `CharArray.full ... |-- CharArray.full ...`

这时不要直接盯着最后一条 `replace_Znth`。

更稳的顺序是：

1. 先看当前假设能不能推出 `i = n`
2. 再用前缀相等性质证明 `l1 = l`
3. 最后再去化简 `replace_Znth` / `replace_nth`

如果一开始不先拿到 `i = n`，后面的尾部归一化通常会越写越乱。

## 19. `Cannot find witness` 经常意味着长度信息还没展开到 `lia` 能直接用的形状

常见卡点：

- `Zlength (x :: l) = ...`
- `Zlength nil = ...`
- “尾部长度等于 1，所以列表只能是 `x :: nil`”

这类地方只写 `lia` 往往不够。

更稳的做法是先显式展开：

- `Zlength_cons`
- `Zlength_nil`
- `Zlength_nonneg`

必要时先单独证明一个局部事实，例如：

- 某个尾表长度恰好为 `1`
- 因此它一定是 `x :: nil`

把这层桥接写出来后，`lia` 才会稳定。

## 20. 多个相似逻辑列表同场时，helper lemma 参数必须显式钉住

在嵌套循环或“保存旧状态 + 当前状态”的 proof 里，经常同时出现：

- 外层循环保存的整体列表
- 内层循环的 base 列表
- 当前 heap 表示列表
- 写入后的候选列表

这时调用局部 helper lemma 不要只写少量索引参数再交给 `eauto` 猜列表参数。即使目标看起来唯一，Coq 也可能把 helper 的 `l_base` 实例化成外层旧列表，留下一个形如“当前 heap list 等于用旧列表拼出来的 sublist 结构”的不可证 side condition。

更稳的写法是：

- 在 `eapply ... with` 中显式给出所有关键列表参数，例如 `(l_base := l_base) (l_cur := l_cur)`
- 对结构等式 side condition 直接 `exact Hshape`
- 对长度等式直接 `exact Hlen` 或 `symmetry; exact Hlen`
- 避免在这种 helper 调用后使用过宽的 `try eauto; try (symmetry; exact H...)`

这类问题的典型症状不是核心语义 lemma 错，而是 `Qed` 报 `Attempt to save an incomplete proof`，`Show` 后剩余目标里出现了错误版本的 sublist 结构。

## 21. merge / two-pointer proof 要先抽 append-last helper，不要在 witness 里展开递归硬证

`merge_sorted_arrays` 的核心 proof 难点不是 separation logic，而是纯 list 语义：

- 写 `a[i]` 后，要证明新输出前缀等于 `merge(sublist 0 (i+1) a, sublist 0 j b)`
- 写 `b[j]` 后，要证明新输出前缀等于 `merge(sublist 0 i a, sublist 0 (j+1) b)`

如果在主 witness 里直接展开 `merge` 递归，proof 会迅速失控。

更稳的做法是先在 `proof_manual.v` 中抽 helper lemma：

- `replace_Znth_app_suffix_head_Z`：把 `replace_Znth k x (prefix ++ sublist k n old)` 归一化成 `(prefix ++ [x]) ++ sublist (k+1) n old`
- `sublist_prefix_snoc_Z`：把 `sublist 0 (i+1) l` 归一化成 `sublist 0 i l ++ [Znth i l 0]`
- `merge_app_a_last`：当所有已消费 `a` 都 `<= x` 且所有已消费 `b` 都 `< x` 时，`merge(a ++ [x], b) = merge(a, b) ++ [x]`
- `merge_app_b_last`：当所有已消费 `a` 都 `<= y` 且所有已消费 `b` 都 `<= y` 时，`merge(a, b ++ [y]) = merge(a, b) ++ [y]`

主 witness 应只做：

- 建立当前 snoc 形式
- 从 invariant 的跨边界关系推出 helper lemma 的 `Forall` 条件
- 调用 helper lemma 改写语义等式
- 交给 `entailer!` 和 `lia` 处理剩余 shape / arithmetic

这个模式适用于 merge、partition、two-sorted-array scan、双指针输出数组等题。

## 22. QCP entailment 里的 disjunction / existential 用大写 tactics

在 QCP assertion entailment 中，目标经常是：

- `P |-- Q1 || Q2`
- `P |-- EX x, Q x`

这时不要直接用 Coq 的 lowercase `left` / `right` / `exists`，否则可能进入 model-level assertion，留下一个形如 `Q m` 的大目标，最后报 `Attempt to save an incomplete proof`。

更稳的写法是：

- 用 `Left` / `Right` 选择 assertion-level disjunction
- 用 `Exists x` 提供 assertion-level existential witness
- 分支前先 `subst` 或 `assert` 出退出等式，例如 `j = m_pre`、`i = n_pre`

如果 `coqtop Show` 里出现目标末尾是 `(...) m`，说明 proof 很可能已经掉进 model-level，需要回到 assertion-level tactic。

## 23. 同一个算法不同 witness 的假设编号不能复制粘贴

`pre_process` 后的假设编号依赖当前 witness 的前置条件顺序。主循环、尾循环、return witness 的编号可能完全不同。

常见错误：

- 从 `entail_wit_2_1` 复制 proof 到 `entail_wit_4`
- 继续使用旧的 `H10` / `H11` / `H14`
- 结果报 `Found no subterm matching ...` 或把 sortedness lemma 应用到错误数组

处理方法：

- 每个新 witness 第一次失败时，用 `coqtop` 停在当前 theorem 后 `Show`
- 明确记录当前 witness 中长度、sortedness、semantic equality、cross-boundary fact 的实际编号
- 对关键事实尽量用 `assert` 命名成语义名，例如 `Hla_snoc`、`Hforalla`、`Hforallb`，减少后续依赖裸编号

不要因为两个 witness 形状相似就默认 hypothesis 编号相同。

## 24. return witness 优先做 full-prefix 和 empty-suffix 归一化

对逐步写满输出数组的题，最终 return witness 往往不是新的语义问题，而是需要把 loop state 归一化成后条件形状。

稳定顺序：

1. 从退出条件推出所有索引到达边界，例如 `i = n`、`j = m`。
2. 推出写入长度到达整段，例如 `k = n + m`。
3. 用 `sublist_self` 把 `sublist 0 n a` 改成 `a`。
4. 用 `sublist_self` 把 `sublist 0 m b` 改成 `b`。
5. 用 `sublist_nil` 把输出未写后缀改成 `nil`。
6. 用 `app_nil_r` 把 heap shape 改成完整输出。
7. 最后用 invariant 保存的 semantic equality 替换 `lout_done`。

不要一开始就证明最终数组相等；先把 prefix/suffix shape 化简到和后条件同形，`entailer!` 才容易收掉。

## 25. `replace_Znth` 最后一步经常卡在 `nat` 索引没有化简

即使在 `Z` 上已经知道索引等于 `0`，展开

- `replace_Znth`

之后，Coq 里常常还残着：

- `replace_nth (Z.to_nat (...)) ...`

如果这个 `Z.to_nat (...)` 不显式改成 `0%nat`，`simpl` 很可能不会继续。

稳定写法是：

1. `unfold replace_Znth`
2. 显式把 `Z.to_nat (...)` 改成 `0%nat`
3. 再 `simpl`

很多看起来像“最后一条列表相等还差一点”的目标，真正缺的就是这一步。

## 26. 局部变量值态到未定义态的权限目标要用 store-undef lemma

循环体内的局部临时变量在 entailment witness 里经常出现：

- 左边：`&( "x" ) # Int |-> v`
- 右边：`&( "x" ) # Int |->_`

`entailer!` 有时不会自动把这个 heap 目标消掉，继续写纯命题证明会导致 bullet 顺序整体错位。

稳定写法是先单独解决这个 separation-logic 子目标：

```coq
apply store_int_undef_store_int.
```

然后再处理后续纯目标。其他类型对应使用 `StoreAux.v` 中同类的 `store_*_undef_store_*` lemma。

## 27. `entailer!` 后的子目标顺序不一定等于规格文本顺序

在 entailment witness 中，`pre_process; entailer!; try lia` 后剩下的目标可能会被重排：

- heap 权限目标可能排在所有 pure 目标之前
- pure 目标可能按 entailment engine 的拆分顺序排列，而不是按 `goal.v` 中右侧断言的文本顺序排列

如果 bullet 脚本出现“当前目标不是预期断言”或“假设匹配失败”，不要继续猜测。

更稳的做法是：

1. 用 `coqtop` 在该 witness 中执行到 `pre_process; entailer!; try lia`
2. `Show.` 查看实际剩余目标顺序
3. 按实际目标顺序重排 bullet
4. 对重复使用的 list / recurrence 结论抽 helper lemma，避免在 witness bullet 里手搓复杂 rewrite

## 28. 溢出 witness 不要只看纯前提，先从栈槽取回 `Int` 范围

如果 `safety_wit` 的目标是类似 `cnt + 1 <= INT_MAX`，而 `pre_process; entailer!` 后纯上下文里没有 `n <= INT_MAX`，不要马上判断为 contract gap。

先在 `entailer!` 之前对相关栈变量使用：

```coq
sep_apply store_int_range.
```

它可以从空间断言 `(&( "n")) # Int |-> n_pre`、`(&( "i")) # Int |-> i` 这类栈槽中恢复 `Int.min_signed <= ... <= Int.max_signed`。之后再结合循环计数的纯上界，例如 prefix count `<= i - 1` 和 `i < n_pre`，通常可以完成自增溢出证明。

## 29. 打开 `sac` 后局部 list 证明避免使用 `[| ...]` 和 `[x]` 语法

`Local Open Scope sac` 可能干扰 Coq 对 list induction/destruct pattern 和 singleton list notation 的解析，表现为：

- `Syntax error: [equality_intropattern] ... expected after 'as'`
- `[x]` 被解析成断言/命题相关语法，而不是 list singleton

在 `proof_manual.v` 的 helper lemma 中，稳定写法是：

- 如果 helper lemma 大量使用普通 Coq list / induction / destruct 语法，优先把 `Local Open Scope sac` 移到这些 helper lemma 之后，只在 generated witness 证明前打开
- 用 `induction xs.` / `destruct xs.`，不要写 `induction xs as [| x xs IH]`
- 用 `cons x nil`，不要写 `[x]`

## 30. Coq 脚本优先用保守写法，尤其少依赖脆弱的 `destruct ... as ...` 形状

自动生成或半自动修改的 proof 中，以下写法更容易在不同环境里出问题：

- 复杂 `intro-pattern`
- 嵌套很深的 bullet
- `destruct ... as ...` 紧跟多个分支和局部重写

更稳的替代是：

- 先 `destruct`
- 再在分支里单独 `rewrite`
- 需要结构信息时，先证明一个局部 `assert`

这样脚本会更长，但通常更稳，也更容易在下一轮编译失败时精确定位 first blocker。

## 31. insertion final witness 要拆成 shape / permutation / order / length 四类 helper

插入排序最后一步 `a[j + 1] = key` 的 witness 容易看起来像一个整体目标：

- 写入后的数组是某个 `replace_Znth`
- 新前缀有序
- 新数组是旧数组的 permutation
- 长度和 heap shape 保持

不要在主 witness 里同时展开这些性质。更稳的拆法是四类 helper：

- shape helper：把 `replace_Znth (j + 1) key l_cur` 改写成 `sublist 0 (j + 1) l_base ++ key :: nil ++ sublist (j + 1) i l_base ++ sublist (i + 1) n l_base`
- permutation helper：只证明 final inserted list 与 `l_base` permutation
- adjacent-order helper：只证明插入后前缀的相邻有序关系，按受影响边界分类讨论
- length helper：只证明 final inserted list 的 `Zlength`

主 witness 只负责：

- `Exists (replace_Znth (j + 1) key l_cur)`
- 用 shape helper 统一 list 表达
- 分别调用 permutation / adjacent-order / length helper
- 处理局部变量权限和简单算术

这样每个 helper 的失败点都很明确，也避免在一个 bullet 中同时面对 `replace_Znth`、`sublist`、`Permutation` 和 `sorted_z`。

## 32. insertion sort 的 sorted proof 优先先证 adjacent order，再在 return 处转成 `sorted_z`

如果 invariant 直接维护 `sorted_z(sublist 0 i l)`，最终插入时通常需要证明 `replace_Znth` 后的结构化 list 仍满足 `sorted_z`，这会牵涉大量 `sublist` 和结构归纳。

更稳定的证明路线是：

1. annotation 层维护相邻有序关系。
2. final insertion witness 只证明相邻有序关系保持。
3. return witness 中一次性调用 helper，把“全数组相邻有序 + 长度覆盖”转成 `sorted_z l`。

这个分层的好处是：

- 循环保持性只需处理局部相邻边
- 未受影响的相邻边可以直接复用 invariant
- `sorted_z` 的结构归纳集中在一个 return helper 中
- witness 里的 list 结构改写明显减少

## 33. 规格递归用 `Z.div`、生成 C 目标用 `Z.quot` 时，先桥接非负除法

数字循环里，Coq 规格可能写成：

```coq
digit_sum_fuel (Z.div n 10) k
```

而 C 表达式生成的目标通常使用 `n ÷ 10`。在 `0 <= n` 且除数为正时，先用 `Z.quot_div_nonneg` 建立二者相等，不要在主 witness 里反复硬改。

推荐拆法：

- 规格 fuel-stability 递归跟随规格本身，使用 `n / 10`
- C 循环保持性和安全性使用生成目标里的 `n ÷ 10`
- 单步语义 lemma 的最后用 `Z.quot_div_nonneg` 把 `n / 10` 替换成 `n ÷ 10`

注意 `replace` 的方向：`replace (n ÷ 10) with (n / 10)` 和 `replace (n / 10) with (n ÷ 10)` 生成的等式方向相反；一个可能需要 `symmetry`，另一个不需要。以当前 Coq 报错里的目标等式为准。

## 34. 不要手写修改生成的 `goal/proof_auto/goal_check`

本地 verify 流程中，`symexec` 生成的文件职责不同：

- `goal.v` 定义 VC 目标
- `proof_auto.v` 存放自动证明结果
- `proof_manual.v` 是手工证明入口
- `goal_check.v` 是最终 include 检查

手工阶段只修改：

- `coq/generated/<name>_proof_manual.v`
- 必要的本地 helper lemma / definition

不要手写修改：

- `<name>_goal.v`
- `<name>_proof_auto.v`
- `<name>_goal_check.v`

如果目标本身明显缺资源、缺纯事实或语义不成立，优先回 annotation / contract 修正，再重新 `symexec`。

## 35. 复用旧 proof 前必须比较 VC 主体

每次重新 `symexec` 或重新生成 VC 后，都要重新检查 manual witness。

旧 proof 只有在下面条件成立时才可复用：

- 当前 VC 和旧 VC 相同
- 或者只存在无关变量名变化，前提、结论和关键资源结构相同

如果 VC 有实质变化，必须重新证明。不要只按 witness 编号复用 proof，因为编号可能稳定但 VC 主体已经变化，也可能编号变化但 VC 主体相同。

**快捷判断（2026-05-25）**：比较 VC 主体之前，先查当前 workspace 的 `logs/workspace_fingerprint.json` 中的 `program_sha256`，与先前成功 workspace 的同字段对比。

- 如果 SHA256 **相同**（且 `input_v` 相同），symexec 输入完全一致，生成的 VC 保证相同，可以直接复用先前 `proof_manual.v`，只需把 `From SimpleC.EE.CAV.verify_<OLD_TIMESTAMP>_<NAME> Require Import` 一行的模块前缀改成当前 workspace 的前缀，proof tactic 主体不需要改动。
- 如果 SHA256 **不同**，才需要逐条比较 VC 主体，按下面的检查点进行。

实操上，VC 主体比较重点是：

- 左侧空间资源是否同形
- 右侧 existential witness 形状是否相同
- 关键 `Znth` / `replace_Znth` / `sublist` 目标是否相同
- 循环分支条件是否相同
- helper lemma 的参数是否仍然对应当前 VC

## 36. `split_pures` 后每个分支都要处理空间上下文

一个容易导致 `coqc` 卡住甚至异常退出的模式是：使用 `split_pures` 后，有些分支没有继续处理空间上下文。

经验规则：

- `split_pures` 后每个分支都必须确认空间侧已经处理
- 常见做法是在每个分支里接 `dump_pre_spatial`
- 如果某个分支看起来只是纯命题，也要确认空间侧已经被正确规整

遇到 `coqc` 长时间卡住或异常崩溃时，检查最近的 `split_pures` 分支是否漏了空间处理。

## 37. safeExec / refinement VC 先分离空间侧，再规范化执行侧

如果目标涉及 `safeExec`、refinement 或 monadic execution predicate，优先按固定 proof skeleton 处理。

稳定顺序：

1. `pre_process.`
2. 先选择必要 `Exists`。
3. 使用 `split_pure_spatial` 分离空间侧和执行侧。
4. 先证明空间侧。
5. 执行侧只在对应 hypothesis 中展开 wrapper。
6. 每次 `unfold ... in H at 1` 或 `unfold_loop in H` 后都运行 `prog_nf in H`。
7. 分支目标用 `safe_choice_l H` 或 `safe_choice_r H` 选择匹配分支。
8. normalized hypothesis 和目标一致时用 `exact H` 收尾。

禁用模式：

- 不要在 `split_pure_spatial` 前展开 `safeExec` 相关定义
- 不要 `unfold ... in *`
- 不要手写 `assert (Hs : safeExec ...)`
- 不要用 `safeExec_bind_reta` / `safeExec_bind` 手工重建执行谓词；优先用 `prog_nf`

## 39. 整数除以 2 的截断商需要局部 helper lemma（2026-05-25）

对使用 `mid = left + (right - left) / 2` 的程序，生成的 `safety_wit` 目标通常形如：

```
INT_MIN <= left + (right - left) ÷ 2 && left + (right - left) ÷ 2 <= INT_MAX
```

标准 `entailer!` 不能自动推出 `0 <= (right - left) ÷ 2 <= right - left`（Coq 的截断除法 `Z.quot`），需要先在 `proof_manual.v` 中定义局部 helper lemma：

```coq
Lemma binary_search_quot2_bounds: forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
Proof. intros; split; [apply Z.quot_nonneg | apply Z.quot_le_upper_bound]; lia. Qed.
```

然后在 `safety_wit_4` 证明中按固定顺序：

```coq
prop_apply (store_int_range (&("left")) left).
prop_apply (store_int_range (&("right")) right).
apply binary_search_quot2_bounds; lia.
entailer!.
```

此 helper 适用于所有 `0 <= x` 时的 `x ÷ 2` 上下界证明，不局限于 binary search；其他需要证明截断商范围的题可以直接复用。

## 40. sortedness / 单调性假设编号在不同 witness 中不固定，优先用 `match goal` 定位（2026-05-25）

在 invariant 保持 witness（`entail_wit_3_1`、`entail_wit_3_2` 等）中，`forall i j, ... => l[i] <= l[j]` 这类 sortedness / 单调性假设由 `pre_process` 自动命名，名字在不同 witness 中不固定（可能是 `H5`、`H8`、`Hsorted` 等）。

不要把一个 witness 中观察到的假设名字直接复制到另一个 witness 里——两次 `pre_process` 后编号可能完全不同（见 §23）。

更稳的写法是用 `match goal` 按假设形状定位：

```coq
match goal with
| Hsorted: forall (i : Z) (j : Z), _ -> Znth i l 0 <= Znth j l 0 |- _ =>
    apply (Hsorted ...); lia
end
```

这样即使假设编号或顺序变化，证明脚本仍然稳定。此模式同样适用于其他"形状已知但名字不稳定"的 sortedness / Forall 类假设。

## 38. 较新 symexec 版本生成的 `proof_manual.v` 格式差异

较新版本的 `symexec` 生成的文件与旧 experience 格式不同，改动如下：

| 位置 | 旧格式 | 新格式 |
|---|---|---|
| 纯命题 | `[| (0 <= n_pre) |]` | `" (0 <= n_pre) "` (string notation) |
| AUXLib import | `List_lemma` | `ListLib` |
| String scope | `Local Open Scope string.` | `Local Open Scope string_scope.` |
| `goal_check.v` | includes strategy proofs | 只 include `goal`/`proof_auto`/`proof_manual` |

**证明影响**：
- `" ... "` 纯命题：`pre_process` 会自动处理；proof tactic 不变
- `ListLib` vs `List_lemma`：`proof_manual.v` 的 header import 用 `ListLib`，`Znth`、`Zlength` 等引理名称不变
- `goal_check.v` 不含 strategy：不需要额外编译 strategy proof 文件，直接按 COMPILE.md 四步编译即可

**实践**：复用旧 experience 的 proof 时，只需把 header import 里的 `List_lemma` 改成 `ListLib`，`string.` scope 改成 `string_scope.`，proof 主体完全可以原样复用。
