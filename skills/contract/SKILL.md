---
name: contract
description: Contract skill，生成验证友好的 `input/<name>.c` / `input/<name>.v`。
---

Contract 的目标只有一个：把原始题意、原始代码和自然语言描述整理成 Verify 可直接消费的规格输入。

开始当前任务前，先阅读：

- `doc/SCOPE.md`
- `doc/PERMISSIONS.md`
- `experiences/general/README.md`
- `experiences/general/CONTRACT.md`

其他文档只在遇到具体阻塞时按需读取。

## 1. 输入

- 原始 C 实现
- 原始题意或自然语言描述
- 约束、边界条件、示例
- 可选的辅助定义草稿

## 2. 输出

- `input/<name>.c`
- `input/<name>.v`，仅当确实需要额外 Coq 定义
- `output/contract_<timestamp>_<name>/logs/reasoning.md`
- `output/contract_<timestamp>_<name>/logs/issues.md`
- `output/contract_<timestamp>_<name>/logs/metrics.md`

## 3. 硬规则

- 先写 `logs/reasoning.md`，再写 `input/<name>.c`
- `input/<name>.c` 只包含目标函数和完整 contract
- 不要提前写 `Inv`、`Assert`、`which implies`、bridge assert、loop-exit assertion
- `input/<name>.v` 只放题目专用 Coq 定义；能不用就不用
- 保持原程序语义不变；若必须改接口，只做验证友好改写
- 日志必须写在当前 `output/contract_<timestamp>_<name>/logs/`
- 如果本次任务更新了任何经验文档，`logs/metrics.md` 必须显式列出更新了哪些经验文件；如果没有更新，也要明确写 `Experience updates: none`

## 4. 最短流程

1. 读原始题意和代码。
2. 写 `logs/reasoning.md`，说明语义、边界、内存与 Coq 依赖判断。
3. 生成 `input/<name>.c`。
4. 判断是否真的需要 `input/<name>.v`。
5. 写 `logs/issues.md` 和 `logs/metrics.md`。

## 5. 完成标准

- `input/<name>.c` 前后条件完整
- 没有混入 Verify 阶段注释
- `.v` 只包含额外逻辑定义
- `reasoning.md`、`issues.md`、`metrics.md` 已写完
