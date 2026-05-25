# Contract Experience

本文件只记录 contract 阶段 contract 写法经验。

阶段职责、输入输出边界、强制规则、完成标准，以 [skills/contract/SKILL.md](../../skills/contract/SKILL.md) 为准；这里不重复这些总规则，只补充 contract 的具体写法和判断细节。

职责边界：

- 只记录 `Require` / `Ensure` / `With` 的写法
- 不记录 invariant/assert/symbolic（见 `INV.md`、`ASSERTION.md`、`SYMEXEC.md`）
- 不记录 manual.v 证明（见 `PROOF.md`）
- 不记录最终 Coq 编译（见 `COMPILE.md`）

## 1. 阅读方式

- 开始 contract 任务时，先从本文件开头顺序读
- 先看 workspace 约定和规格接入方式
- 再看后面的具体规格经验
## 2. 合同写作重点

- 前置条件里优先明确输入域、长度、内存形状和溢出边界
- 后置条件只写函数语义结果，不提前写 verify 阶段的中间断言
- `With` 只绑定后置确实需要引用的逻辑变量，避免无用绑定

## 3. 方式一：直接 `Extern Coq`

适用场景：
- 仓库公共库里已经有现成的 Coq 数学函数
- C 规格只需要直接引用这个函数
- 不需要额外包装成题目专用 `pre/spec`

典型写法：

```c
/*@ Extern Coq (factorial: Z -> Z) */

int factorial(int n)
/*@ Require
      0 <= n && n <= 10 && emp
    Ensure
      __return == factorial(n@pre) && emp
*/
```

使用原则：
- 优先先查仓库里是否已经有可复用的 Coq 名字
- 如果公共定义已经足够表达题意，就不要再额外创建 `input/<name>.v`
- 这种情况下，`input/<name>.v` 应留空或根本不创建

## 4. 方式二：题目专用 `.v` 桥接

适用场景：
- 题目语义不是一个现成公共函数就能表达
- 需要把自然语言题意包装成稳定的 `pre/spec`
- 需要额外定义辅助关系、辅助谓词或题目专用逻辑名

典型写法分两部分。

`input/<name>.c` 中：

```c
/*@ Extern Coq (factorial: Z -> Z)
               (bfact_coq: Z -> Z) */
/*@ Extern Coq (problem_139_pre_z: Z -> Prop) */
/*@ Extern Coq (problem_139_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_139 */
```

然后在规格里直接用：

```c
/*@ Require
      problem_139_pre_z(n) &&
      1 <= n && n <= 10 && emp
    Ensure
      problem_139_spec_z(n@pre, __return) && emp
*/
```

对应的 `coins_139.v` 中再做桥接：

```coq
Definition problem_139_pre_z (n : Z) : Prop := ...
Definition problem_139_spec_z (n r : Z) : Prop := ...
```

使用原则：
- `.v` 只负责桥接和补题目专用逻辑，不要把本该直接写在 C 规格里的简单内容都搬进去
- 如果只是缺一个公共数学函数名，不要为了形式统一强行新建 `.v`
- 只有当 C 规格明显需要题目专用语义层时，才创建 `input/<name>.v`

## 5. 选择规则

- 公共数学函数已存在：优先用“直接 `Extern Coq`”
- 题目需要专用 `pre/spec` 包装：使用“题目专用 `.v` 桥接”
- 能不用 `.v` 就不用 `.v`；只有确实缺桥接层时才新建

## 6. 先定数学语义，再定前后条件

更稳的 contract 顺序是：

1. 先写清楚函数的数学语义
2. 再决定前置条件需要限制什么
3. 再决定是否需要高层/低层两层规格
4. 最后才把这些落成 `Require` / `Ensure` / `With`

如果数学语义本身没说清楚，后面的 contract 往往会反复返工。

## 7. 前置条件优先约束最终结果，而不是穷举中间状态

对单调累加、乘法递推、前缀构造这类题，前置条件优先约束“最终不会溢出”，通常比逐项约束中间状态更短、更稳。

例如：

- `factorial` 用 `0 <= n <= 10`
- `sum` / `sum2` 这类题优先约束最终闭式值在 `int` 范围内

如果中间状态天然单调且不超过最终状态，这种写法通常足够支撑 Verify 阶段的 safety witness。

## 8. 有抽象语义和具体表示时，优先分两层规格

如果一个题同时存在：

- 对外更自然的抽象语义
- 对实现更自然的具体表示

就优先分成高层语义规格和低层表示规格，不要一开始把两种职责揉在一个谓词里。

这样做的好处是：

- Contract 产出的 contract 对用户更稳定
- Verify 只需要在局部展开实现真正会用到的表示
- 高层语义不会被底层指针或局部更新污染

## 9. 能用 shape-only 时，不要强行把值语义写满

如果题目当前阶段真正需要的是：

- 内存安全
- 结构保持
- 局部可写性

而不是精确内容等价，那么 contract 应优先考虑 shape-only 谓词，不要在 Contract 阶段把值语义写得过满。

这能显著减少 Verify 阶段的 invariant 和 proof 负担。

## 10. 缺 `.v` 的判断标准

判断是否需要 `input/<name>.v`，优先问：

1. 现有公共 Coq 定义能否直接表达题意？
2. 是否真的需要题目专用 `pre/spec` 包装？
3. 是否需要额外的辅助关系或中间语义层？

只有这几个问题里至少一个必须回答“是”，才创建题目专用 `.v`。

参考：
- `factorial` 这类简单整数语义，适合直接 `Extern Coq`
- `QualifiedCProgramming/QCP_examples/humaneval/IntClaude/C_139.c`
- `QualifiedCProgramming/QCP_examples/humaneval/IntClaude/coins_139.v`

## 11. C 字符串 contract 不能只写“末尾有一个 0”

如果函数语义依赖 C 风格字符串终止规则，例如：

- `strlen`
- `string_copy`
- 扫描到 `'\0'` 为止的匹配或计数

那么 contract 不能只写：

- `CharArray::full(s, n + 1, app(l, cons(0, nil)))`

这只说明“最后还接了一个 `0`”，并不排除 `l` 内部提前出现 `0`。

对这类函数，如果后置条件需要把 `l ++ [0]` 当成完整字符串语义，就必须在前置条件里显式加入：

```c
(forall (k: Z), (0 <= k && k < n) => l[k] != 0)
```

否则 Verify 阶段通常只能证明：

- 程序会在遇到某个 `0` 时停下

却不能证明：

- 它停下的位置就是最后一个 terminator
- 整个目标缓冲区最终等于 `app(l, cons(0, nil))`

判断标准：

- 如果程序行为是“遇到第一个 `0` 就停止”，而后置条件又要求完整复制/处理整个 `l ++ [0]`
- 那么 contract 必须补“前缀无内部 `0`”

不要把这个问题留到 Verify 或 manual proof 阶段；这是 Contract 层就该固定的语义前提。

## 12. 字符串扫描类题如果后条件要恢复整个字符串，前置条件必须能推出退出位置是最终 terminator

对这类程序：

- `strlen`
- `string_copy`
- 扫描到 `'\0'` 后返回、复制、计数、判断

Verify 阶段的 return witness 往往都会走到同一个桥接点：

- 先证明退出位置 `i` 就是最终 terminator 位置
- 再把“已处理前缀”恢复成完整字符串

如果 contract 不能推出这一点，proof 常见表现是：

- `symexec` 成功
- loop invariant 也能写出来
- 但 `return_wit` 最后只剩一条 `replace_Znth` / `CharArray.full` 的纯 list 目标，始终收不掉

因此，contract 设计时要先问：

1. 当前前置条件能否推出“遇到的第一个 `0` 就是最后一个 terminator”？
2. 如果后置条件要求完整恢复 `l ++ [0]`，是否已经显式排除了内部 `0`？

如果答案是否定的，就先改 contract，不要把这个缺口留给 Verify 阶段。

## 13. 避免在函数级 `Require` 中用顶层析取表达简单数值域

如果 `Ensure` 或后续 loop invariant 需要使用 `x@pre`，函数级 `Require` 中的顶层析取可能触发 QCP frontend 的 old-value 绑定问题。

已观察到的失败形态：

```c
/*@ Require
      0 <= a &&
      0 <= b &&
      (a != 0 || b != 0) &&
      emp
    Ensure
      gcd_iterative_spec(a@pre, b@pre, __return) && emp
*/
```

`symexec` 在生成 VC 前报：

```text
Old value at `pre' is not determined
```

对照实验表明：

- `a@pre` / `b@pre` 作为 imported Coq predicate 参数本身可以工作
- 去掉顶层析取后，`symexec` 可以生成 VC
- 在 `0 <= a && 0 <= b` 下，把 `(a != 0 || b != 0)` 改写成等价的 `0 < a + b` 后，`symexec` 也可以生成 VC

因此，Contract 阶段遇到简单数值域的“至少一个非零”“至少一个条件成立”时，优先使用无顶层析取的等价表达，尤其是后置条件需要 `@pre` 时。

GCD 的推荐写法：

```c
/*@ Require
      0 <= a &&
      0 <= b &&
      0 < a + b &&
      emp
    Ensure
      gcd_iterative_spec(a@pre, b@pre, __return) && emp
*/
```

不要把这个问题留给 Verify 阶段；这是 contract 编码形状导致的 frontend 问题，不是 loop invariant 或 manual proof 能修复的 Coq 目标。
