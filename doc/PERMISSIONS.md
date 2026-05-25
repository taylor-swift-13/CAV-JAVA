# Verify File Permissions

本文件只定义 Verify 阶段的读写边界。

## 1. 前提

Verify 的前提是：

- Contract 已经产出 `input/<name>.c`
- 如有需要，Contract 也已产出 `input/<name>.v`

Verify 默认只消费这些正式输入，不负责重写它们。

## 2. 当前任务的两类工作区

每次处理某个 `input/<name>.c` 时，都必须先确定：

- 当前任务对应的唯一 workspace：`output/verify_<timestamp>_<name>/`
- 当前任务对应的唯一 annotated 工作副本：`annotated/verify_<timestamp>_<name>.c`
- 这两者必须同名对齐：workspace 基名是 `verify_<timestamp>_<name>`，annotated 文件名也必须正好是 `verify_<timestamp>_<name>.c`

除非用户明确授权，否则 Verify 的写操作只能落在这两处。

## 3. 默认允许读取

- `input/<name>.c`
- `input/<name>.v`，如果存在
- `skills/verify/SKILL.md`
- `experiences/general/README.md`
- `experiences/general/SYMEXEC.md`
- `experiences/general/ASSERTION.md`
- `experiences/general/INV.md`
- `experiences/general/PROOF.md`
- `experiences/general/COMPILE.md`
- `doc/COQ_PROOF_GUIDE.md`
- `doc/SCOPE.md`

## 4. 按需允许读取

- `doc/predict/INDEX.md` 及其子文档：只在处理对应数据结构或程序形态时读取
- `doc/retrieval/INDEX.md`：只在当前步骤卡住、需要检索相似例子时读取
- `experiences/end-end/`：允许作为优先检索的完整样例库
- `QualifiedCProgramming/QCP_examples/` 下其他例子：只有当 `experiences/end-end/` 没有足够接近的例子时，才允许扩大范围读取
- `QualifiedCProgramming/tutorial/`：只在当前步骤确实缺少教程级说明时读取

## 5. 当前任务允许人工修改

- `annotated/verify_<timestamp>_<name>.c`
- `output/verify_<timestamp>_<name>/coq/generated/<name>_proof_manual.v`
- `output/verify_<timestamp>_<name>/coq/deps/` 下为当前 workspace 准备的依赖 `.v`
- `output/verify_<timestamp>_<name>/logs/workspace_fingerprint.json`
- `output/verify_<timestamp>_<name>/logs/annotation_reasoning.md`
- `output/verify_<timestamp>_<name>/logs/proof_reasoning.md`
- `output/verify_<timestamp>_<name>/logs/issues.md`
- `output/verify_<timestamp>_<name>/logs/metrics.md`

## 6. 当前 workspace 内只读文件

允许读取、编译检查、由工具覆盖，但不允许人工修改：

- `output/verify_<timestamp>_<name>/original/<name>.c`
- `output/verify_<timestamp>_<name>/original/<name>.v`，如果存在
- `output/verify_<timestamp>_<name>/coq/generated/<name>_goal.v`
- `output/verify_<timestamp>_<name>/coq/generated/<name>_proof_auto.v`
- `output/verify_<timestamp>_<name>/coq/generated/<name>_goal_check.v`
- `output/verify_<timestamp>_<name>/coq/generated/<name>_proof_check.v`，如果存在
- `output/verify_<timestamp>_<name>/logs/qcp_run.log`

## 7. 默认禁止修改

除非用户明确要求，否则禁止修改：

- `input/`
- `raw/`
- 不属于当前任务的 `annotated/*.c`
- 其他题目的 workspace
- 仓库级脚本、README、配置文件
- 公共头文件、公共 Coq 库、公共 strategy 文件
- `QCP_examples/` 下与当前任务无关的其他例子
- `tutorial/` 文件

## 8. 阻塞时如何分流

如果继续推进必须：

- 改写 `input/<name>.c`
- 新增或修改 `input/<name>.v`
- 调整原始题意对应的正式 contract

就应将其视为 Contract 问题，而不是在 Verify 中越权修改。
