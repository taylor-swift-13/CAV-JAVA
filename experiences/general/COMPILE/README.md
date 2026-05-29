# Compile Experience

本文件只记录 verify 阶段的 Coq 编译经验。

常见入口：

- 编译前先确认目录：看 1
- 编译参数必须包含两部分：看 2
- 有题目专用 `.v` 时，必须显式给 `original/` load path：看 3
- 长编译命令优先用 bash 数组，不要硬拼引号：看 4
- 当前项目的稳定编译模板：看 5
- 公共 strategy 缺失时再 fallback 到 `coq/deps/`：看 6
- 逻辑前缀必须一致：看 7
- 编译顺序固定：看 8
- `goal_check` 之前不要算完成：看 9
- 重新确认轮次跳过完整 recompile 的条件：看 10
- 编译后必须清理：看 11

## 1. 编译前先确认目录

- 工作目录必须是 `QualifiedCProgramming/SeparationLogic`
- verify workspace 仍然位于仓库顶层 `output/verify_<timestamp>_<name>/`
- 也就是说：QCP 的 Coq 编译从子仓库 `QualifiedCProgramming/SeparationLogic` 发起，但输入/输出 workspace 路径都指向外层仓库
- 当前题目的 generated 文件在 `output/verify_<timestamp>_<name>/coq/generated/`
- 默认直接复用公共 `examples/*.vo`
- 只有公共 strategy 预编译产物缺失时，才回退到 `output/verify_<timestamp>_<name>/coq/deps/`

## 2. 编译参数必须包含两部分

必须同时带上：

- `_CoqProject` 里的基础 `-R`
- 当前 workspace 的额外 `-R`

基础参数缺失时，最常见报错是：

- `Cannot find a physical path bound to logical path int_auto with prefix AUXLib`

这说明少了 `_CoqProject` 里的 `-R auxlibs AUXLib` 等基础 load-path。

## 3. 有题目专用 `.v` 时，必须显式给 `original/` load path

如果当前题目有：

- `output/verify_<timestamp>_<name>/original/<name>.v`

就不能只给 `generated/` 的逻辑前缀。

还必须显式加入：

- `-Q "$ORIG" ""`

否则 `Require Import <name>` 或题目专用数学定义在编译 `proof_manual.v` / `goal_check.v` 时会找不到。

## 4. 长编译命令优先用 bash 数组，不要硬拼引号

长 `coqc` 命令里同时有：

- 多个 `-R`
- `-Q "$ORIG" ""`
- workspace 变量
- 逻辑前缀变量

这时优先用 bash 数组，例如：

- `BASE=(...)`
- `EXTRA=(...)`

原因：

- 避免引号地狱
- 避免路径里空格或变量展开出错
- 命令更容易复制、删改和调试

不要在很长的一行字符串里手工嵌套引号。

## 5. 当前项目的稳定编译模板

在 `QualifiedCProgramming/SeparationLogic` 下执行：

```bash
REPO_ROOT=/path/to/CAV-JAVA
WS="$REPO_ROOT/output/verify_<timestamp>_<name>"
NAME=<name>
GEN="$WS/coq/generated"
ORIG="$WS/original"
LP=SimpleC.EE.CAV.verify_<timestamp>_<name>
BASE=(
  -R SeparationLogic SimpleC.SL
  -R unifysl Logic
  -R sets SetsClass
  -R compcert_lib compcert.lib
  -R auxlibs AUXLib
  -R examples SimpleC.EE
  -R StrategyLib SimpleC.StrategyLib
  -R Common SimpleC.Common
  -R fixedpoints FP
  -R MonadLib MonadLib
  -R listlib ListLib
)
EXTRA=(
  -Q "$ORIG" ""
  -R "$GEN" "$LP"
)

coqc "${BASE[@]}" -Q "$ORIG" "" "$ORIG/${NAME}.v"
coqc "${BASE[@]}" "${EXTRA[@]}" "$GEN/${NAME}_goal.v"
coqc "${BASE[@]}" "${EXTRA[@]}" "$GEN/${NAME}_proof_auto.v"
coqc "${BASE[@]}" "${EXTRA[@]}" "$GEN/${NAME}_proof_manual.v"
coqc "${BASE[@]}" "${EXTRA[@]}" "$GEN/${NAME}_goal_check.v"
```

如果当前题目没有专用 `.v`，就跳过第一条 `coqc`。

不要把 `WS` 再写回 `QualifiedCProgramming/QCP_examples/CAV/output/...` 或 `output/...` 的相对子路径；现在 workspace 已经提升到外层仓库，编译命令应始终使用外层绝对路径。

## 6. 公共 strategy 缺失时再 fallback 到 `coq/deps/`

- 如果公共 `examples/*.vo` 已存在，直接复用，不要再复制到 workspace
- 只有公共 strategy 编译产物缺失或当前环境读不到时，才创建 `coq/deps/`
- fallback 时，把需要的 strategy `.v` 复制到当前 workspace 的 `coq/deps/`
- 然后把编译参数改成：`EXTRA=(-Q "$ORIG" "" -R "$DEPS" SimpleC.EE -R "$GEN" "$LP")`

## 7. 逻辑前缀必须一致

- `coq/deps/` 固定用 `-R "$DEPS" SimpleC.EE`
- `coq/generated/` 固定用 `-R "$GEN" SimpleC.EE.CAV.verify_<timestamp>_<name>`

不要混用不同前缀编出来的 `.vo`，否则常见报错是：

- `contains library X and not library Y`

## 8. 编译顺序固定

1. 先编 `coq/deps/` 里缺的依赖
2. 再编题目专用 `original/<name>.v`，如果存在
3. 再编 `goal.v`
4. 再编 `proof_auto.v`
5. 再编 `proof_manual.v`
6. 最后编 `goal_check.v`

## 9. `goal_check` 之前不要算完成

完成标准必须同时满足：

- `goal.v` 通过
- `proof_auto.v` 通过
- `proof_manual.v` 通过
- `goal_check.v` 通过
- `proof_manual.v` 无 `Admitted.`
- `proof_manual.v` 无新增 `Axiom`

## 10. 重新确认轮次跳过完整 recompile 的条件（2026-05-26）

在 verify 的"precautionary retry"轮次中，如果前一轮**已经确认** Final Result: Success，且进入当前轮次时以下条件全部满足：

1. `coq/generated/` 只含 `.v` 文件，无 `.vo/.glob/.vok/.vos/.aux` 中间产物
2. `proof_manual.v` 中 `Admitted.` 个数为 0（`grep -c "Admitted"` 退出码为 1）
3. `workspace_fingerprint.json` 中 `verification_status` 为 `goal_check_passed`
4. `metrics.md` 的 Final Result 为 Success

此时**不必再跑完整 5 步 coqc**。直接核对上述四项，记录为"No new blockers found"后退出即可。

理由：每次 coqc 会生成新的中间产物（`.vo/.glob` 等），随即又需要 cleanup；在 16 个重复轮次中，这一"编译 → 生成中间产物 → 清理"的循环每轮耗时约 1–2 分钟，累计超过 25 分钟，最终因整体 timeout（exit 124）导致 verify 阶段标记为 Fail，尽管证明本身在第一轮 ~22 分钟内就已完成。

唯一例外：如果某轮因 API Overload 或其他故障中途终止（中间产物可能残留），才需要重跑 coqc 以恢复干净状态。

## 11. 编译后必须清理

- `coq/` 下删除非 `.v` 的编译中间产物
- `input/` 下删除非 `.v`、非 `.c` 的编译中间产物
- 如果环境限制导致删不掉，要写进 `logs/issues.md`
