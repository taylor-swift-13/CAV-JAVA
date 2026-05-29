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

**读取范围白名单。** 除当前任务自身的 I/O（`input/<name>.c`、`input/<name>.v`、当前 `annotated/verify_<timestamp>_<name>.c`、当前 workspace `output/verify_<timestamp>_<name>/` 下的文件）外，所有「查文档 / 查经验 / 找参考样例」的读取**只能**落在下面三棵目录树内：

- `doc/`
- `experiences/`
- `QualifiedCProgramming/QCP_examples/`

不要为了查工具用法或找参考解去读这三棵树以外的任何目录（详见 §3.1）。下面列出的是这三棵树里最常用的文件：

- `input/<name>.c`
- `input/<name>.v`，如果存在
- `skills/verify/SKILL.md`
- `experiences/general/README/README.md`
- `experiences/general/SYMEXEC/README.md`
- `experiences/general/ASSERTION/README.md`
- `experiences/general/INV/README.md`
- `experiences/general/PROOF/README.md`
- `experiences/general/COMPILE/README.md`
- `doc/COQ_PROOF_GUIDE.md`
- `doc/SCOPE.md`

## 4. 按需允许读取

- `doc/predict/INDEX.md` 及其子文档：只在处理对应数据结构或程序形态时读取
- `doc/retrieval/INDEX.md`：只在当前步骤卡住、需要检索相似例子时读取
- `experiences/end-end/`：允许作为优先检索的完整样例库
- `QualifiedCProgramming/QCP_examples/` 下其他例子：只有当 `experiences/end-end/` 没有足够接近的例子时，才允许扩大范围读取

## 3.1 禁止读取

这些目录/文件**不在**读取白名单内，读它们只会浪费 turn、拖慢简单任务，一律不要读：

- `scripts/` 下的编排脚本（`run_verify.py`、`run_pipeline.py`、`agent_loop.py`、`coq_runner.py` 等）——它们是调用你的 harness，与单题验证无关。
- `QualifiedCProgramming/` 下除 `QCP_examples/` 以外的目录（`SeparationLogic/`、`tutorial/`、`linux-binary/` 等库源码与工具）。编译时 cwd 在 `SeparationLogic/`、跑 `symexec` 时 cwd 在 `QualifiedCProgramming/`，那是「运行工具」不是「读源码」；命令模板见 `experiences/general/SYMEXEC/README.md §0` 与 `experiences/general/COMPILE/README.md §5`，不要去读这些目录反推用法。
- 当前 workspace 的完整 harness transcript（`logs/agent_stdout_*.jsonl`、`logs/agent_prompt_*`）。retry 轮只读 `logs/agent_last_message_*`、`logs/agent_stderr_*`、`logs/continue.md` 和 generated/annotated 文件。
- `git log` / `git show` 历史考古：不要靠翻 git 历史找参考解；参考解只按 `doc/retrieval/INDEX.md` 在 `experiences/end-end/` 或 `QCP_examples/` 里检索。

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
