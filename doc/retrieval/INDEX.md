# Retrieval Index

本文件只记录检索规则。

## 1. 检索顺序

- 先检索仓库内的 `experiences/end-end/`
- 如果这里没有足够接近的完整例子，再放宽到 `QualifiedCProgramming/QCP_examples/`
- 不要一开始就全仓库泛搜

## 2. 什么时候才检索

- 只有当前步骤卡住、缺少相似题思路、谓词用法、witness 结构或 proof pattern 时才检索
- 如果当前输入和当前 workspace 已经足够推进，就不要先去搜例子

## 3. 检索时先看什么

每个 workspace 的最小检索单元是：

- `logs/workspace_fingerprint.json`

建议顺序：

1. 先看 `keywords`
2. 再看 `semantic_description`
3. 最后才读 `annotation_reasoning.md`、`proof_reasoning.md`、`issues.md` 和相关 `.v`

## 4. fingerprint 要写什么

每个 workspace 的 `logs/workspace_fingerprint.json` 至少应包含：

- workspace 名称
- 输入文件
- 函数名
- `semantic_description`
- `keywords`

## 5. `semantic_description` 怎么写

至少写清楚：

- 程序在做什么
- 输入输出的核心关系
- 关键控制结构
- 边界行为
- 是否修改内存

## 6. `keywords` 怎么用

- `keywords` 必须来自受控词表，不要自由发明同义词
- 先用 `keywords` 过滤，再用自然语言描述判断是否真的相似

## 7. `keywords` 受控词表

- 历史 git 版本里的受控 key 只有这些：
  - `algorithm_family`
  - `control_flow`
  - `data_shape`
  - `semantic_intent`
  - `proof_pattern`
  - `numeric_properties`
  - `edge_case_behavior`
  - `verification_status`

- `algorithm_family` 只允许：
  - `identity`
  - `selection`
  - `counting`
  - `accumulation`
  - `arithmetic_series`
  - `factorial`
  - `prefix_sum`
  - `simulation`
  - `search`
  - `two_pointers`
  - `dynamic_programming`
  - `greedy`
  - `recursion`

- `control_flow` 只允许：
  - `straight_line`
  - `if`
  - `ternary`
  - `for_loop`
  - `while_loop`
  - `do_while`
  - `nested_loop`
  - `recursion`

- `data_shape` 只允许：
  - `scalar_only`
  - `array`
  - `string`
  - `pointer`
  - `struct`
  - `linked_list`
  - `tree`
  - `graph`

- `semantic_intent` 只允许：
  - `return_input`
  - `return_max`
  - `count_iterations`
  - `sum_1_to_n`
  - `sum_even_series`
  - `compute_factorial`
  - `preserve_input`
  - `in_place_update`

- `proof_pattern` 只允许：
  - `pure_arithmetic`
  - `loop_invariant`
  - `case_split`
  - `termination_by_bound`
  - `closed_form`
  - `monotonicity`
  - `range_bound`
  - `heap_reasoning`

- `numeric_properties` 只允许：
  - `nonnegative_input`
  - `overflow_guard`
  - `int_range`
  - `monotone_accumulator`
  - `exact_closed_form`

- `edge_case_behavior` 只允许：
  - `returns_zero_on_nonpositive`
  - `returns_input_on_nonpositive`
  - `defined_for_nonnegative_only`
  - `branch_on_order`
  - `empty_loop_possible`

- `verification_status` 只允许：
  - `goal_check_passed`
  - `proof_check_passed`
  - `manual_witness_needed`
  - `auto_proof_contains_admitted`
  - `generated_goal_contains_axioms`

- `keywords` 只允许使用以上历史 key 和 value
- 一个 key 可以对应单个字符串，或由上述历史 value 组成的列表
- 如果当前任务不需要某个维度，就省略该 key，不要发明新 key，也不要发明新 value

## 8. 允许展开阅读的样例范围

- `experiences/end-end/` 下的样例可以直接展开阅读
- 如果 `experiences/end-end/` 不够，再去 `QualifiedCProgramming/QCP_examples/` 下读取其他相关例子
- 仍然优先选择和当前目标最接近的题型、数据结构、witness 结构或 proof pattern
[text](../../experiences/end-end/array_contains)
