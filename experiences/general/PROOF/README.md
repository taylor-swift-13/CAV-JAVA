# Proof Experience

本文件只记录 `coq/generated/<name>_proof_manual.v` 的手工证明经验。

常见入口：

- 证明范围：看 1
- 开始前先读当前目标：看 2
- 先做最短证明骨架（try-first 起手式）：看 3
- 先分清卡点类型：看 4
- 编译失败时先看完整 proof state：看 5
- 卡住时去例子库检索：看 6
- 主 witness 不要硬顶 tactic，先抽 helper lemma：看 7
- `Cannot find witness` 往往不是神秘错误，而是 side condition 不显式：看 8
- Coq 脚本尽量写保守，不要过度依赖自动化和自动命名：看 9
- `entailer!` 收不掉时先整理上下文：看 10
- 失败记录必须写首个稳定错误：看 11
- 不允许绕过证明：看 12
- 改结构后必须重新 symbolic：看 13
- `proof_auto.v` 已经定义的 lemma，不要在 `proof_manual.v` 里重复定义：看 14
- 如果 return witness 同时出现 `x` 和 `x_pre`，先检查 annotation 是否保留了 `x == x@pre`：看 15
- `Cannot find witness` 经常意味着长度信息还没展开到 `lia` 能直接用的形状：看 16
- QCP entailment 里的 disjunction / existential 用大写 tactics：看 17
- 同一个算法不同 witness 的假设编号不能复制粘贴：看 18
- 局部变量值态到未定义态的权限目标要用 store-undef lemma：看 19
- `entailer!` 后的子目标顺序不一定等于规格文本顺序：看 20
- 打开 `sac` 后局部 list 证明避免使用 `[| ...]` 和 `[x]` 语法：看 21
- Coq 脚本优先用保守写法，尤其少依赖脆弱的 `destruct ... as ...` 形状：看 22
- 不要手写修改生成的 `goal/proof_auto/goal_check`：看 23
- 复用旧 proof 前必须比较 VC 主体：看 24
- `split_pures` 后每个分支都要处理空间上下文：看 25
- sortedness / 单调性假设编号在不同 witness 中不固定，优先用 `match goal` 定位：看 26
- 较新 symexec 版本生成的 `proof_manual.v` 格式差异：看 27
- 直线函数没有 entail_wit 目标，proof_manual.v 始终为空：看 28
- `entailer!` 后残留 `(p <> NULL)` 这类纯条件 → contract 层缺非空，不要在证明里硬抠：看 29

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

## 3. 先做最短证明骨架（try-first 起手式）

按 VC 形状直接套以下模板、立即跑 `coqc`、读错误信息再迭代。**首版尝试前 read/grep 累计不超过 10 次**，symexec 已经给了 lemma 名和类型，足够猜一版。

| VC 形状 | Tactic 模板 |
|--------|------------|
| 直线 / 标量 entail | `Proof. pre_process; entailer!; try lia. Qed.` |
| sll cons 展开（`partial_solve_wit`：`sll p (cons x l) \|-- EX y, ...`） | `Proof. pre_process. simpl sll. Intros y. Exists y. cancel. Qed.`（暴露的 `“ x <> NULL ”` 用 `Intros_p _` 丢弃） |
| sll cons 折回（`return_wit`：`cells ** sll y l \|-- sll p (cons x l)`） | `Proof. pre_process. simpl sll. Exists <y>. split_pure_spatial. - cancel. - entailer!. Qed.` |

**关键约束**：sll cons 折回要求 LHS 已有 `“ p_pre <> 0 ”` 纯条件（contract 写了 `p != 0`）。如果 `entailer!` 留下未解的 `(p <> NULL)`——参见 §42 和 `../CONTRACT/1/pointer-deref-needs-non-null.md`，是 contract 缺非空、verify 不能修。

`Admitted` 可以**临时**留着，让你能继续编译其他 lemma；最终判定只看 `proof_manual.v` 是否 `Admitted`-free。

每一轮失败后把新的失败点、原因判断和下一步计划追加写入 `logs/proof_reasoning.md`。

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

## 15. 如果 return witness 同时出现 `x` 和 `x_pre`，先检查 annotation 是否保留了 `x == x@pre`

典型现象：

- `return_wit` 看起来只差把当前参数名改回 `*_pre`
- proof 里缺的不是 list / arithmetic，而是“这个标量参数从头到尾没变”

处理顺序：

1. 先看 loop invariant 和 loop-exit assertion 是否显式保留了 `x == x@pre`
2. 如果没有，回 annotation 层补这个不变关系
3. 清理 generated 文件并重新跑 `symexec`

不要在 `proof_manual.v` 里硬证一个 annotation 本该直接保留的参数恒等关系。

## 16. `Cannot find witness` 经常意味着长度信息还没展开到 `lia` 能直接用的形状

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

## 17. QCP entailment 里的 disjunction / existential 用大写 tactics

在 QCP assertion entailment 中，目标经常是：

- `P |-- Q1 || Q2`
- `P |-- EX x, Q x`

这时不要直接用 Coq 的 lowercase `left` / `right` / `exists`，否则可能进入 model-level assertion，留下一个形如 `Q m` 的大目标，最后报 `Attempt to save an incomplete proof`。

更稳的写法是：

- 用 `Left` / `Right` 选择 assertion-level disjunction
- 用 `Exists x` 提供 assertion-level existential witness
- 分支前先 `subst` 或 `assert` 出退出等式，例如 `j = m_pre`、`i = n_pre`

如果 `coqtop Show` 里出现目标末尾是 `(...) m`，说明 proof 很可能已经掉进 model-level，需要回到 assertion-level tactic。

## 18. 同一个算法不同 witness 的假设编号不能复制粘贴

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

## 19. 局部变量值态到未定义态的权限目标要用 store-undef lemma

循环体内的局部临时变量在 entailment witness 里经常出现：

- 左边：`&( "x" ) # Int |-> v`
- 右边：`&( "x" ) # Int |->_`

`entailer!` 有时不会自动把这个 heap 目标消掉，继续写纯命题证明会导致 bullet 顺序整体错位。

稳定写法是先单独解决这个 separation-logic 子目标：

```coq
apply store_int_undef_store_int.
```

然后再处理后续纯目标。其他类型对应使用 `StoreAux.v` 中同类的 `store_*_undef_store_*` lemma。

## 20. `entailer!` 后的子目标顺序不一定等于规格文本顺序

在 entailment witness 中，`pre_process; entailer!; try lia` 后剩下的目标可能会被重排：

- heap 权限目标可能排在所有 pure 目标之前
- pure 目标可能按 entailment engine 的拆分顺序排列，而不是按 `goal.v` 中右侧断言的文本顺序排列

如果 bullet 脚本出现“当前目标不是预期断言”或“假设匹配失败”，不要继续猜测。

更稳的做法是：

1. 用 `coqtop` 在该 witness 中执行到 `pre_process; entailer!; try lia`
2. `Show.` 查看实际剩余目标顺序
3. 按实际目标顺序重排 bullet
4. 对重复使用的 list / recurrence 结论抽 helper lemma，避免在 witness bullet 里手搓复杂 rewrite

## 21. 打开 `sac` 后局部 list 证明避免使用 `[| ...]` 和 `[x]` 语法

`Local Open Scope sac` 可能干扰 Coq 对 list induction/destruct pattern 和 singleton list notation 的解析，表现为：

- `Syntax error: [equality_intropattern] ... expected after 'as'`
- `[x]` 被解析成断言/命题相关语法，而不是 list singleton

在 `proof_manual.v` 的 helper lemma 中，稳定写法是：

- 如果 helper lemma 大量使用普通 Coq list / induction / destruct 语法，优先把 `Local Open Scope sac` 移到这些 helper lemma 之后，只在 generated witness 证明前打开
- 用 `induction xs.` / `destruct xs.`，不要写 `induction xs as [| x xs IH]`
- 用 `cons x nil`，不要写 `[x]`

## 22. Coq 脚本优先用保守写法，尤其少依赖脆弱的 `destruct ... as ...` 形状

自动生成或半自动修改的 proof 中，以下写法更容易在不同环境里出问题：

- 复杂 `intro-pattern`
- 嵌套很深的 bullet
- `destruct ... as ...` 紧跟多个分支和局部重写

更稳的替代是：

- 先 `destruct`
- 再在分支里单独 `rewrite`
- 需要结构信息时，先证明一个局部 `assert`

这样脚本会更长，但通常更稳，也更容易在下一轮编译失败时精确定位 first blocker。

## 23. 不要手写修改生成的 `goal/proof_auto/goal_check`

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

## 24. 复用旧 proof 前必须比较 VC 主体

每次重新 `symexec` 或重新生成 VC 后，都要重新检查 manual witness。

旧 proof 只有在下面条件成立时才可复用：

- 当前 VC 和旧 VC 相同
- 或者只存在无关变量名变化，前提、结论和关键资源结构相同

如果 VC 有实质变化，必须重新证明。不要只按 witness 编号复用 proof，因为编号可能稳定但 VC 主体已经变化，也可能编号变化但 VC 主体相同。

开始 proof 前，先用 `logs/workspace_fingerprint.json` 的四字段检索端到端样例：

- `keywords.problem_kind`
- `keywords.data`
- `keywords.pattern`
- `semantic_description`

如果 `experiences/end-end/<function-name>/` 存在，优先读取它的 fingerprint；否则按 `doc/retrieval/INDEX.md` 扫描 `experiences/end-end/*/logs/workspace_fingerprint.json`。fingerprint 只用于找到相关候选，不证明当前 VC 与旧 VC 相同。

实操上，VC 主体比较重点是：

- 左侧空间资源是否同形
- 右侧 existential witness 形状是否相同
- 关键 `Znth` / `replace_Znth` / `sublist` 目标是否相同
- 循环分支条件是否相同
- helper lemma 的参数是否仍然对应当前 VC

## 25. `split_pures` 后每个分支都要处理空间上下文

一个容易导致 `coqc` 卡住甚至异常退出的模式是：使用 `split_pures` 后，有些分支没有继续处理空间上下文。

经验规则：

- `split_pures` 后每个分支都必须确认空间侧已经处理
- 常见做法是在每个分支里接 `dump_pre_spatial`
- 如果某个分支看起来只是纯命题，也要确认空间侧已经被正确规整

遇到 `coqc` 长时间卡住或异常崩溃时，检查最近的 `split_pures` 分支是否漏了空间处理。

## 26. sortedness / 单调性假设编号在不同 witness 中不固定，优先用 `match goal` 定位（2026-05-25）

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

## 27. 较新 symexec 版本生成的 `proof_manual.v` 格式差异

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
- `goal_check.v` 不含 strategy：不需要额外编译 strategy proof 文件，直接按 `../COMPILE/README.md` 四步编译即可

**实践**：复用旧 experience 的 proof 时，只需把 header import 里的 `List_lemma` 改成 `ListLib`，`string.` scope 改成 `string_scope.`，proof 主体完全可以原样复用。

## 28. 直线函数没有 entail_wit 目标，proof_manual.v 始终为空（2026-05-27）

对没有循环、没有中间 `Assert`/`which implies` 注释、没有内存副作用的直线函数（straight-line program），symexec 只会生成 `safety_wit` 和 `return_wit` 目标，两者都由 `proof_auto.v` 的 `Admitted` 自动解决。`entail_wit` 目标只在 `Assert`/`which implies` 或循环 invariant 边界处产生——直线函数没有这些切割点，因此 `proof_manual.v` 只会包含 header，没有任何 theorem。

实践效率规则：
- 接手直线函数的 verify workspace 时，不必打开 `proof_manual.v` 搜索待证 theorem——直接确认 `proof_manual.v` 只有 header、`proof_auto.v` 中全是 `Admitted`、四步 compile replay 通过，即可按 §1 跳过 manual proof 阶段。
- 判断"是否直线函数"的标准：无 `for`/`while`/`do-while`、无 `Assert`/`which implies` 中间注释、无内存写操作（只有 `return`）。满足上述三条即可直接预判 `proof_manual.v` 为空。

## 29. `entailer!` 后残留 `(p <> NULL)` 这类纯条件 → contract 层缺非空，不要在证明里硬抠（2026-05-28）

折叠 sll 类 shape predicate 的 `return_wit` 时，如果 `entailer!` 留下未解的 `(p_pre <> NULL)` 之类纯条件，**不要尝试用 `sep_apply valid_store_int` / `valid_store_ptr` 从字段 mapsto 抽非空**——会徒劳：

- `isvalidptr_int x = x >= 0 ∧ aligned_4 x ∧ x + 3 ≤ max_unsigned`（`CommonAssertion.v:63`），`0` 满足全部三条；
- `isvalidptr` / `isvalidptr_int64` 同形状，同样不排除 `0`；
- QCP 库里没有「`x # T |-> v |-- “ x <> 0 ”`」这种通用引理。

根因是 contract 层缺指针非空——symexec 没法从 `sll(p, cons(...))` 自动把 `“ p <> NULL ”` 抽到 wit 的 LHS。修法见 **../CONTRACT/README.md §15**：让前条件显式带 `p != 0`，或调整后条件结构让 partial 行为被吸收，让生成的全部 VC 都可证。

### 在 verify workspace 里的具体响应

- 把这个阻塞写进 `logs/issues.md`：`(<wit_name>) entailer! leaves (p_pre <> NULL); contract lacks non-null — see experiences/general/CONTRACT/1/pointer-deref-needs-non-null.md`；
- **不要**自己改 contract / annotated C 绕过；那是 Contract 阶段的固定义务，verify 阶段越权改 contract 会让审计阶段反告 contract drift；
- 把 `Final Result: Fail` 写到 `logs/metrics.md`，按 §1「contract gap」边界正常退出。
