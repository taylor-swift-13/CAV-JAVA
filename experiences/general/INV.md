# Invariant Experience

本文件只记录循环 invariant 的设计经验。

不记录：

- `Assert` / `which implies` 细节（见 `ASSERTION.md`）
- symbolic 执行流程（见 `SYMEXEC.md`）
- manual proof（见 `PROOF.md`）

常见入口：

- 写 invariant 前的 reasoning 标准：看 1
- invariant 控制点位置：看 2
- 状态量闭式表达：看 3
- 扫描类循环：看 4
- 退出后能否推出后条件：看 7
- nested loop：看 8
- 参数不变关系：看 9
- 数组逐步写入 / DP：看 10
- merge / 双指针：看 11、12
- 排序前缀 / insertion sort：看 13、15
- `for` 循环初始化边界和 skip-loop：看 14

## 1. 写 invariant 前，必须先做充分的自然语言 reasoning，并检查能否证出后条件

如果当前函数根本不需要补任何 `Inv` / `Assert`，就不要机械地生成 `annotation_reasoning.md`；直接跳过这一阶段。

在真正写 `Inv` 之前，必须先用自然语言把思路写清楚，而不是直接试错式地改注释。

至少要先分析：

- 当前循环变量各自表示什么：已处理部分、待处理部分、还是下一步位置
- 哪些程序变量、数组段、指针区间是每轮都要保留的
- 后条件真正需要的语义是什么
- 当前准备写的 invariant 是否会把这些语义保留下来

如果题目较复杂，这份 reasoning 应先落到当前 workspace 的 `logs/annotation_reasoning.md`，再开始改 `annotated/verify_<timestamp>_<name>.c`。

写任何 invariant 之前，还必须逐条检查它是否同时满足下面三件事：

- 初始化成立：循环第一次进入判断点前，invariant 就已经成立
- 保持性成立：假设本轮开始时 invariant 成立，执行一轮循环体后，下轮判断点前仍成立
- 退出可用：循环条件为假时，invariant 和退出条件能直接或经一个很小的 exit assertion 推出后条件

如果这三件事里有一个答不上来，就不要继续写 Coq proof，先回到注释层重做 reasoning。

一个 invariant 只做到“看起来每轮都能保持”是不够的；还必须保证最终能证出后条件。

更稳的标准是：

- invariant 保留的内容，正好覆盖后条件需要的核心语义
- 退出时只需要很少的算术整理或一个最小的 loop-exit assertion

如果退出时还需要大量重建语义，通常说明 invariant 太弱；如果 invariant 里塞了很多和后条件无关的东西，通常说明 invariant 太脏。

## 2. invariant 要写在真实控制点上

`for` / `while` 的 invariant 写的是“进入循环判断点前”的状态。

因此优先写成：

- 已处理前缀
- 下一次待处理位置
- 当前累加器/状态量对应的闭式表达

不要把 invariant 写成“本轮循环体执行结束后应该成立什么”。

## 3. 先找状态量的闭式表达

循环题的关键通常是：

- 索引到底代表“已完成”还是“待处理”
- 累加器表示哪一段结果
- 当前数据结构被拆成了哪几段

闭式表达选对之后，很多 witness 会直接退化成纯算术。

## 4. 扫描类循环优先建模成“状态量 = 已处理前缀摘要”

对单向扫描类循环，最稳的 invariant 模板通常不是“当前变量大概表示某种结果”，而是明确写成：

- 状态量等于已处理前缀的某个摘要

常见摘要包括：

- 前缀和
- 前缀最大值
- 前缀最小值
- 已处理元素个数
- 已处理前缀是否满足某个布尔性质

例如 max/min 扫描题，优先把 `ret` 建模成：

- `ret == prefix_max`
- 或 `ret == max_list_nonempty(sublist 0 i l)`

而不是只写“`ret` 不小于某些元素”这类过弱关系。

这样写的好处是：

- 初始化容易对齐到第一个元素或空前缀
- 保持性可以直接对应“加入一个新元素后的摘要更新”
- 退出时更容易直接推出后条件

## 5. invariant 只保留后续真正需要的信息

常见需要保留的内容：

- 边界关系
- 参数不变关系
- 已处理部分的语义
- 未处理部分的 shape

不需要的内容不要提前塞进去，否则 witness 会变脏。

## 6. 指针/区间推进问题优先用 “context + focus”

对这类程序：

- 链表遍历
- 树下降
- 双指针
- 分段处理

优先考虑 invariant 由两部分组成：

- 已处理上下文
- 当前焦点

两者拼回整体语义。

## 7. 退出时要能直接通向后条件

设计 invariant 时，先问自己：

- 循环退出条件和 invariant 拼起来，能不能直接推出后条件
- 还缺不缺一个显式 loop-exit assertion

如果退出后还需要大量额外重建语义，说明 invariant 往往还不够贴题。

## 8. nested loop 必须分别有自己的 invariant

典型错误现象：

- `Error: Lack of assertions in some paths for the loop!`

常见原因：

- 只给外层循环写了 invariant
- 内层循环依赖外层语义，但自己没有局部状态描述

处理方法：

- 外层循环描述跨轮保持的全局语义
- 内层循环描述当前扫描区间/当前位置/局部单调性或局部最大值之类的中间性质
- 不要指望外层 invariant 自动覆盖内层所有路径

## 9. invariant 缺“参数不变关系”会直接污染 witness

典型现象：

- `return_wit` 左右两侧只差 `a` 和 `a@pre`
- witness 里反复重建某个形参未改变

处理方法：

- 在 invariant 中显式加入需要保持不变的参数关系
- 修改后立刻重新 `symexec`

这类问题属于 invariant 缺信息，不要拖到 `proof_manual.v` 再补救。

## 10. 对数组/DP 题，invariant 先分“已定义前缀”和“未定义后缀”

如果循环逐步写数组，优先把内存分成两段：

- 已经写好的前缀：`*_seg` 或对应完整语义
- 尚未写入的后缀：`undef_seg`

处理方法：

- 先让 shape 上闭合
- 再在已写前缀上叠加值语义

不要一开始就试图把整段数组都写成完整值语义；这很容易在初始化早期就卡住 invariant 校验。

## 11. 双指针归并类题不能只记录“已合并前缀”，还要记录跨边界顺序历史

`merge_sorted_arrays` 这类题难的根本原因是：程序每轮只比较当前 `a[i]` 和 `b[j]`，但 proof 里要证明“把当前元素追加到已合并结果末尾”是合法的。

只写下面这些信息通常不够：

- `0 <= i <= n`
- `0 <= j <= m`
- `k == i + j`
- `lout_done == merge(sublist(0, i, a), sublist(0, j, b))`

因为当选择 `a[i]` 时，证明需要知道所有已经消费的 `b[0..j)` 都小于当前和未来相关的 `a`；当选择 `b[j]` 时，也需要知道已经消费的 `a[0..i)` 都不大于当前和未来相关的 `b`。

更稳的 invariant 要把两类历史关系显式留下来：

- consumed `b` 与 future `a` 的严格顺序关系
- consumed `a` 与 future `b` 的非严格顺序关系

这两个关系不是装饰性信息，而是证明 merge-prefix 语义保持性的核心桥梁。没有它们，`symexec` 可能仍能生成 VC，但 manual proof 会在 `lout_done ++ [x] = merge(...)` 这类纯 list 目标上卡死。

设计这类 invariant 时建议先用自然语言写清楚：

- `lout_done` 精确等于哪两个已消费前缀的 merge
- `out` 的 heap shape 是 `app(lout_done, sublist(k, n + m, old_out))`
- `k` 是否始终等于 `i + j`
- 两个输入数组是否保持原始长度和值
- tie rule 是选择 `a` 还是选择 `b`，跨边界关系必须和 tie rule 一致

尤其要注意 `<=` 和 `<` 的方向：如果代码在 `a[i] <= b[j]` 时选择 `a`，那么 consumed `a` 到 future `b` 可以是 `<=`，而 consumed `b` 到 future `a` 往往需要 `<`，否则 append-last helper lemma 的条件会对不上。

## 12. 多阶段循环要为每个阶段保留足够的阶段切换事实

归并程序通常有三个循环：

- 主双指针循环
- 复制 `a` 剩余元素的尾循环
- 复制 `b` 剩余元素的尾循环

难点在于第二、第三个循环不是独立扫描，它们继承了主循环退出时的历史语义。

常见错误是：

- 第二个循环一开始就假设 `j == m`，但真实控制流可能是 `i == n` 退出主循环
- 第三个循环一开始就假设 `i == n`，但没有把前面阶段保存的 merge-prefix 语义带过去
- 尾循环只保留 `k == i + j`，却丢失跨边界顺序关系，导致尾部 append 证明无法完成

处理方法：

- 主循环退出后先用 disjunction 或阶段 assertion 区分 `i == n` 与 `j == m`
- 每个尾循环的 invariant 仍然保留完整的 `lout_done == merge(consumed_a, consumed_b)`
- 尾循环继续保留跨边界关系，即使其中一侧已经到达边界；这些关系在 proof 中会变成 vacuous 或用于 append-last lemma
- 退出到 return witness 前，要能直接推出 `i == n`、`j == m`、`k == n + m`

## 13. 排序前缀 invariant 可优先携带相邻有序关系

对插入排序这类每轮只在局部移动元素、最终需要 `sorted_z` 的数组排序题，循环 invariant 里直接携带 `sorted_z(sublist 0 i l)` 可能让最终插入/交换 witness 变成大段结构化 list proof。

更稳的做法是携带等价但更局部的相邻有序关系：

- `forall k, 0 <= k && k + 1 < i => l[k] <= l[k + 1]`

这样保持性只需按受影响的相邻边分类讨论，未受影响的边直接复用旧 invariant；退出时再用一个 Coq helper 从相邻有序关系和长度推出 `sorted_z`。这通常比在每个循环保持 witness 中直接证明 `sorted_z` 的 `sublist` / `replace_Znth` 结构变换更稳定。

## 14. `for` 循环 invariant 要按“初始化后、判断前”的状态写边界

C 的 `for (init; cond; step)` invariant 位于执行 `init` 后、检查 `cond` 前的控制点，不是进入循环体后的状态。

典型坑是：

- `for (i = 1; i < n; ++i)`
- precondition 允许 `n == 0`
- invariant 却写成 `i <= n`

初始化后 `i == 1`，此时还没有检查 `i < n`。如果 `n == 0`，`i <= n` 是假的，但程序本身合法并且会跳过循环。

处理方法：

- 循环头 invariant 的边界要允许 skip-loop 初始状态，例如 `i <= n + 1`
- 如果 return witness 仍需要非空分支的强边界，再额外写条件事实，例如 `n > 0 => i <= n`
- 退出处再结合 loop guard false 和条件事实恢复后条件需要的边界

不要把“循环体会执行时成立的边界”写成“循环判断点总成立的 invariant”。

## 15. 插入排序内循环优先建模成 shifted-hole

插入排序内循环不是普通交换排序，它的核心状态是“拿出 `key` 后，右移元素形成一个 hole”。

更稳的 inner invariant 应显式保存：

- `l_base`：进入本轮外循环时的基准数组
- `l_cur`：当前 heap 数组
- `key`：被拿出的元素
- `j` 和 `i` 对应的 hole 位置
- `l_cur` 与 `l_base` 的 shifted-hole 结构关系

典型结构是：

- 前缀未受影响：`sublist 0 (j + 2) l_base`
- 被右移区间：`sublist (j + 1) i l_base`
- 后缀未受影响：`sublist (i + 1) n l_base`

这比只写“当前前缀仍有序”更适合证明：

- 一次右移后 heap shape 怎么变化
- `Znth j l_cur` 和 `Znth j l_base` 如何对应
- 最终 `a[j + 1] = key` 后如何恢复完整数组
- permutation 如何从局部插入结构推出

如果 invariant 没有显式保存 shifted-hole，final insertion witness 往往会退化成很难控制的 `replace_Znth` / `sublist` 大等式。

## 17. 双分支区间收缩循环（二分查找类）优先用严格不等式作为 range-exclusion invariant（2026-05-25）

对使用 `left / right` 双指针的区间收缩循环（典型：`while (left <= right)` + 分支 `left = mid+1` / `right = mid-1` + 命中时立即返回），优先把两个 range-exclusion 事实写成**严格不等式**：

- `forall i, 0 <= i < left => l[i] < target`
- `forall i, right < i < n => target < l[i]`

**为什么用严格 `<` 而非 `!=`**：当 `a[mid] < target` 时，单调性给出 `l[k] <= l[mid] < target`，因此所有 `k <= mid` 都满足 `l[k] < target`；`a[mid] > target` 分支同理。`l[i] < target` 直接蕴含 `l[i] != target`，退出时无需额外改写；若只写 `!=`，保持性证明还需要额外的 case split 联系 `<` 与 `=`。

**变量边界**（必须覆盖 n=0 skip-loop 的初始状态）：

- `0 <= left && left <= n`（允许 `left == n` 表示"已超出右边界"）
- `-1 <= right && right < n`（允许 `right == -1` 表示空区间，对应 n=0 时 `right = n-1 = -1`）
- `left <= right + 1`（**不是** `left <= right`；允许空区间；退出条件 `left > right` 等价于 `left >= right + 1`，与此写法天然对应）

**退出状态**：`left > right` 结合两个 range-exclusion 事实，对任意 `k ∈ [0,n)`，要么 `k < left`（由第一条覆盖），要么 `right < k`（由第二条覆盖），直接推出 `forall k, l[k] != target`；无需额外 loop-exit assertion。

**不要**在 `return -1` 前加 loop-exit assertion：`mid` 在循环前声明、n=0 时未初始化；加了之后 symexec 会报 `Fail to Remove Memory Permission of mid`。

## 16. `i + 1 < n` 扫描循环不要把 `n <= INT_MAX` 硬塞进 invariant

如果输入 contract 没有显式给 `n <= INT_MAX`，但循环 guard 或数组访问使用 `i + 1 < n`，不要为了证明 `i + 1 <= INT_MAX` 直接在 invariant 里加入：

- `n <= INT_MAX`
- 或需要从 `n <= INT_MAX` 初始化的无条件 `i + 1 <= INT_MAX`

这会把 invariant 初始化 VC 变成从纯 contract 和 `IntArray.full` 证明 `n <= INT_MAX`，通常不可证。更稳的做法是在 invariant 中保留源级条件边界，让 safety witness 在带有局部栈变量的上下文里用 `store_int_range (&("n")) n_pre` 取得 C `int` 范围。

常见形状：

- `for (i = 0; i + 1 < n; ++i)` 可用 `(0 < n => i + 1 <= n)`
- `while` 初始化为 `i = 1` 且允许 `n <= 1` skip-loop 时，可用 `(1 < n => i + 1 <= n)`，同时保留 `i <= n + 1`

保持性通常来自 loop guard：旧的 `i + 1 < n` 在 `i++` 后推出新的 `i + 1 <= n`。退出证明再用 guard false，例如 `i + 1 >= n`，桥接到后条件需要的索引范围。
