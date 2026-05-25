# Symexec Experience

本文件只记录 symbolic execution / `qcp` 相关经验。

不记录：

- `Assert` / `which implies` 的写法（见 `ASSERTION.md`）
- 循环 invariant 的设计（见 `INV.md`）
- manual proof（见 `PROOF.md`）
- Coq 编译与 load-path（见 `COMPILE.md`）

常见入口：

- 自动 verify 进程卡住：看 1
- annotation 改动后重新 `symexec`：看 2
- `symexec` 失败先查控制点：看 3
- `symexec` 成功后分流到 proof 还是 annotation：看 4、13
- annotated 工作副本路径：看 5
- 公共 strategy / `coq/deps`：看 6
- witness 形状脏，怀疑 annotation 信息组织错：看 7
- `goal_check` 没过不能算完成：看 8
- metrics / issues 记录要求：看 9、10
- invariant 很强导致前端变慢：看 12
- `Extern Coq` 名称和 C 函数名重名：看 14
- 重新生成 VC 后不能盲用旧 proof：看 15
- manual / auto witness 分流：看 16

## 1. 自动 verify 进程卡住时，不要继续空等

典型现象：

- `codex_stderr` 持续出现 `channel closed`
- stdout/stderr 长时间不再增长
- 外层脚本还活着，但没有新产物

处理方法：

- 先停止自动进程，接管当前 workspace
- 检查是否已经生成：
  - 当前任务对应的 `annotated/verify_<timestamp>_<name>.c`
  - `coq/generated/<name>_goal.v`
  - `coq/generated/<name>_proof_auto.v`
  - `coq/generated/<name>_proof_manual.v`
- 已生成的产物优先复用，不要重复开新 workspace

## 2. 每次注释改动后都必须重新 `symexec`

只要你改了下面任一内容，就必须重新跑 `symexec`：

- `Inv`
- `Assert`
- `which implies`
- loop-exit assertion
- 任何会改变 VC 形状的中间注释

不要继续沿用旧的 `goal`、`proof_auto`、`proof_manual`、`goal_check`。

重新跑当前 workspace 的 `symexec` 之前，必须先清理旧的 generated 文件：

- `coq/generated/<name>_goal.v`
- `coq/generated/<name>_proof_auto.v`
- `coq/generated/<name>_proof_manual.v`
- `coq/generated/<name>_goal_check.v`
- `coq/generated/<name>_proof_check.v`，如果存在

否则工具可能因为旧的 `proof_manual.v` 已存在而拒绝更新，导致新的注释和旧的 witness 混在一起。

## 3. `symexec` 失败时，先检查注释与控制点是否对齐

先检查：

- invariant 写的是进入循环判断点的状态，还是循环体执行后的状态
- `Assert` 是否放在真正的阶段切换点
- 局部展开是否和当前读写语句匹配
- 退出条件是否已经被显式固定

很多 symbolic 失败不是 proof 问题，而是注释没有贴住程序控制点。

## 4. `symexec` 成功后先分流，不要机械回注释层

`symexec` 成功后，先判断剩余问题属于哪一层。

如果剩下的是这些问题，就不要再回注释层：

- 纯 list witness
- 纯 arithmetic witness
- Coq side condition
- 只差 helper lemma、rewrite、case split

这类问题已经进入 proof 阶段，继续改注释通常只会浪费时间。

只有在下面这些现象出现时，才应回注释层：

- witness 明显缺 shape / ownership 信息
- `return_wit` 或 `entail_wit` 反复重建“参数未变”“数组未变”这类语义
- 退出后条件需要大量额外语义，说明 invariant 太弱
- witness 里出现和控制点不对应的旧状态、错位状态

判断原则：

- 缺程序语义，回注释层
- 缺纯命题桥接，不回注释层

## 5. 顶层 `annotated/` 目录就是为避免头文件路径报错

verify 的实际工作副本固定放在：

- `annotated/verify_<timestamp>_<name>.c`

它和 `input/` 是同层目录，所以像 `../../verification_stdlib.h` 这类相对头文件路径通常可以直接沿用，不需要再在每个 workspace 里手改 include。

如果还报头文件找不到，优先检查：

- 当前 `qcp` / `symexec` 跑的是不是这个顶层 `annotated/*.c`
- 是否误用了旧 workspace 里的历史 `annotated` 副本

不要把这类问题回退成修改 `input/<name>.c`。

## 6. 公共 strategy 预编译后，不要再为每题重复 staging `coq/deps/`

如果下面这些公共产物已经存在：

- `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/int_array_strategy_goal.vo`
- `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/int_array_strategy_proof.vo`
- `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/uint_array_strategy_goal.vo`
- `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/uint_array_strategy_proof.vo`
- `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/undef_uint_array_strategy_goal.vo`
- `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/undef_uint_array_strategy_proof.vo`
- `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/array_shape_strategy_goal.vo`
- `QualifiedCProgramming/SeparationLogic/examples/QCP_demos_LLM/array_shape_strategy_proof.vo`

后续 verify 应直接复用 `QualifiedCProgramming/SeparationLogic/examples/` 下的公共产物，不要再把这些文件复制到当前 workspace 的 `coq/deps/`。

只有公共编译产物缺失，或当前环境读不到它们时，才回退到 workspace-local `coq/deps/`。

## 7. witness 形状脏，通常是注释层信息组织不对

如果生成的 witness 很绕、重复、纯命题很乱，优先怀疑：

- invariant 缺参数不变关系
- `Assert` 放错位置
- shape/value 语义混写
- 不该展开的谓词提前展开了

先回去整理当前任务的 `annotated/*.c`，通常比在 `proof_manual.v` 里硬扛更便宜。

## 8. 当前 `goal_check` 没过时，不能把任务算完成

即使已经有：

- `goal.v`
- `proof_auto.v`
- `proof_manual.v`

也不能直接判完成。

必须再确认：

- `goal_check.v` 编译通过
- `proof_manual.v` 无 `Admitted.`
- `proof_manual.v` 无新增 `Axiom`

## 9. `metrics.md` 里要单独记 `symexec`

verify 阶段的 `metrics.md` 至少要单列：

- `symexec_start`
- `symexec_end`
- `symexec_elapsed`

## 10. `issues.md` 里要保留 symbolic 过程问题

即使最后修好了，也要记：

- 现象
- 原因
- 处理
- 结果

## 11. 新增题目本地 Coq helper 不是 verify 阶段的首选修复

如果当前 `input/<name>.v` 不存在，而 verify 阶段为了绕开复杂断言临时在 annotated 文件中新增 `Extern Coq` / `Import Coq`，要谨慎。

已观察到的风险：

- `symexec` 可能在正常 startup 日志前直接 segfault
- 问题发生在 VC 生成前，无法进入 manual proof
- 即使 helper 理论上能让 Coq proof 更清楚，也可能不如使用前端原生断言形状稳定

处理顺序：

1. 优先尝试把断言改写成前端支持的原生形式，例如拆分 implication、减少 disjunction、减少单条断言里的嵌套 conjunction。
2. 只有输入阶段已经提供题目 `.v`，或已有相同模式的稳定样例时，才优先走 helper import。
3. 如果新增 helper 后 `symexec` 立即 segfault，应回退到无 helper 的 annotation 形状，并把 helper 尝试记录到当前 workspace 的 `issues.md`。

## 12. 复杂 invariant 让 `symexec` 变慢时，先简化前端表达形状，不要先删语义

`merge_sorted_arrays` 暴露了一个典型问题：正确语义需要较强 invariant，但强 invariant 如果写成前端不擅长的形状，会让 `symexec` 长时间 CPU-bound 或在 VC 生成前失败。

不要第一反应就删除关键语义。应先检查表达形状：

- 是否在 ownership 中反复使用复杂的 `@pre` 算术表达式
- 是否在 implication guard 内使用自由数组下标
- 是否在量词中使用 bracket notation，例如 `la[i]`
- 是否把多个 disjunction / implication / conjunction 堆在一条 assertion 中
- 是否把 shape 和 value 语义混在一个过大的谓词里

更稳的改写顺序：

1. ownership 长度优先用当前状态的简单表达式，例如 `n + m`，再用纯命题保存它与 pre-state 的关系。
2. 对带边界的 ghost list 访问，优先写成显式 `Znth(index, list, 0)`，不要依赖前端从 guard 推断 bracket notation 的数组大小。
3. 对阶段切换，优先拆成较小的 loop-exit assertion 或分阶段 invariant，不要把所有情况塞进一个巨大 invariant。
4. 如果 `symexec` 成功且剩余目标是纯 list / arithmetic witness，就不要再回注释层删语义；此时应进入 manual proof。

判断标准是：

- 删除后会丢失后条件所需语义的内容不能删
- 只影响前端解析和 VC 生成复杂度的表达形式应改写

## 13. `symexec` 成功后如果 witness 是 merge/list 语义，不要误判为 annotation 失败

双指针归并类题在 `symexec` 成功后，常见剩余目标是：

- `replace_Znth` 写入输出前缀后的 heap list 归一化
- `merge(spec_prefix_a, spec_prefix_b)` 与 `old_prefix ++ [current]` 的等式
- `sublist` 追加一个末尾元素的等式
- 已消费前缀与未消费后缀的顺序关系保持

这些目标通常属于 proof 阶段，不是 symbolic execution 阶段。

只有当 witness 明显缺少下面信息时，才回到 invariant：

- 输出数组的完整 heap shape
- `lout_done` 与已消费前缀的语义等式
- 输入数组未修改的长度和值
- 跨边界顺序历史
- 阶段切换时的 `i == n` 或 `j == m`

如果这些信息都在 VC 里，剩下的困难基本就是 helper lemma 和 conservative Coq proof，不要反复改 annotation。

## 14. `Extern Coq` 数学符号不能和 C 函数符号重名

典型现象：

```text
fatal error: Redefinition of `factorial' as different kind of symbol
```

常见触发形状：

```c
/*@ Extern Coq (factorial: Z -> Z) */

int factorial(int n)
/*@ Ensure __return == factorial(n@pre) && emp */
```

这是 `symexec` 前端符号表冲突，不是 invariant、assertion 或 manual proof 问题。优先在 Contract 阶段避免这种输入形状：让 C 实现函数名和数学 Coq 函数名不同，例如 C 函数用 `fac`，规格里的数学函数仍用 `factorial`。

如果已经在 Verify retry 中接管旧 workspace，且用户要求继续同一 workspace，可在 active annotated 工作副本中只改 C 实现符号名来验证同一函数体和同一数学规格；不要改 `input/<name>.c`，并且必须在 `continue.md`、`annotation_reasoning.md`、`issues.md`、`metrics.md` 里明确记录这是为了绕开前端符号冲突。

## 15. 重新 `symexec` 后必须重新检查 VC 主体

每次重新运行本地 `symexec` 后，都必须把最新生成的 `goal/proof_auto/proof_manual/goal_check` 当作唯一事实来源。

不要只按 witness 编号复用旧 proof。编号可能稳定但 VC 主体已经变化，也可能编号变化但目标主体相同。

复用旧 proof 前至少检查：

- theorem 名字是否仍存在
- theorem 的前提资源是否相同
- theorem 的右侧目标是否相同
- 关键 ghost list、数组 segment、边界条件是否相同
- 变化是否只是无关变量名

如果 VC 有实质变化，进入 `proof_manual.v` 重新证明。

## 16. auto-solved VC 不进入 manual proof

`symexec` 生成后先分清：

- `proof_auto.v` 已经解决的 VC
- `proof_manual.v` 中还需要手工证明的 theorem

不要把 auto-solved VC 复制到 `proof_manual.v` 里重新证明，也不要定义和 `proof_auto.v` 中同名的 `proof_of_<name>_*` lemma。

开始 manual proof 前先读：

- `coq/generated/<name>_proof_auto.v`
- `coq/generated/<name>_proof_manual.v`
- `coq/generated/<name>_goal_check.v`

这样可以避免 `goal_check.v` 同时 include auto/manual 后出现重复 label。

## 17. `With` ghost 变量不要写成 `@pre`

如果 `symexec` 在函数体第一行或 contract 结束位置报：

```text
fatal error: Expected C expression ... Now parsing : n with type :2
```

并且当前位置附近有 `With l n` 这类 ghost 变量，优先检查 postcondition、invariant、assertion 里是否把 ghost 写成了 `n@pre`。`@pre` 应用于 C 参数或局部变量；`With` 引入的 ghost 值应直接写 `n`、`l`。字符串样例里的 ghost 长度通常在 `Ensure` 和 invariant 中保持为 `n`，而不是 `n@pre`。

处理顺序：

1. 不要先进入 Coq proof；这是前端解析问题。
2. 在 active annotated 工作副本里把 ghost-state 的 `n@pre` 改成 `n`，保留真实 C 参数的 `old_c@pre`、`new_c@pre`、`s@pre` 等。
3. 重新运行 `symexec`，因为该修改会改变生成 VC。

## 18. `int_array_def.h` 是不应该放进 annotated C 的头文件

如果 `input/<name>.c` 包含 `#include "../../int_array_def.h"`（或其他路径的 `int_array_def.h`），在 `annotated/` 工作副本里必须删掉这行。

原因：
- `int_array_def.h` 是给 C 编译器用的 C-level 定义（不是标准库头文件）
- `symexec` 的 include search path 找不到这个文件，无论设置哪个 `-slp` 或 include 路径
- `IntArray::full`、`IntArray::missing_i` 等 separation logic 谓词是 symexec 内置的，通过 `load_builtin_int_array_strategy_lib` 加载，不需要任何头文件声明

操作：
1. 在 `annotated/verify_<timestamp>_<name>.c` 里删掉 `#include "../../int_array_def.h"` 这一行
2. 保留 `verification_stdlib.h` 和 `verification_list.h` 的 include（改成不带 `../../` 的 bare 名字即可）
3. 重新跑 `symexec`

不要尝试：修改 `-slp` 路径、设置 `INCLUDE_PATH` 环境变量、在 QCP 目录下创建 symlink 等——这些均无效。
