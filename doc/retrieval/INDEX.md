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

检索单元有两种，schema 共享（都用 `semantic_description` + `keywords`）：

- **end-end 样例**：每个 `experiences/end-end/<case>/logs/workspace_fingerprint.json`（完整 workspace + 路径）
- **专题经验**：每个 `experiences/general/<NAME>/<N>/<slug>.fingerprint`（指向同目录 `<slug>.md`，只放 `semantic_description` 和 `keywords` 两字段）

建议顺序：

1. 先看 `keywords`
2. 再看 `semantic_description`
3. 命中 general：直接读对应 `<N>/<slug>.md`（短）
4. 命中 end-end：再展开 `annotation_reasoning.md`、`proof_reasoning.md`、`issues.md` 和相关 `.v`

大模型查找相关端到端样例时，只使用四字段 fingerprint：

- `keywords.problem_kind`
- `keywords.data`
- `keywords.pattern`
- `semantic_description`

前三个字段是受控词表，用来粗筛候选；`semantic_description` 是自由文本，用来判断候选是否真的和当前题相关。

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

`semantic_description` 是 `keywords` 之外唯一的自由文本检索字段。`keywords` 负责粗筛；`semantic_description` 负责判断两个算法题是否真的相似。

## 6. `keywords` 怎么用

- `keywords` 必须来自受控词表，不要自由发明同义词
- 优先按 `problem_kind` / `data` / `pattern` 过滤，再用 `semantic_description` 判断是否真的相似
- 如果三个 keyword 全部一致，优先展开该样例
- 如果只有两个 keyword 一致，只有在 `semantic_description` 的输入输出关系和控制结构也相似时才展开
- 如果只有一个或零个 keyword 一致，默认不展开，除非用户明确要求扩大搜索

## 7. `keywords` 受控词表

为算法题检索，只保留 3 个 key：

- `problem_kind`
- `data`
- `pattern`

`problem_kind` 描述题目要计算什么，只允许：

- `identity`
- `min_max`
- `count`
- `sum`
- `product`
- `search`
- `compare`
- `transform`
- `partition`
- `sort`
- `prefix`
- `dp`
- `math`

`data` 描述主要数据形态，只允许：

- `scalar`
- `array`
- `string`
- `matrix`
- `linked_list`
- `tree`
- `graph`

`pattern` 描述算法骨架，只允许：

- `straight_line`
- `branch`
- `single_loop`
- `nested_loop`
- `two_pointers`
- `sliding_window`
- `prefix_scan`
- `binary_search`
- `recursion`
- `state_machine`

`keywords` 只允许使用以上 key 和 value。一个 key 可以对应单个字符串，或由上述 value 组成的列表（用列表表示该经验跨多个题型/数据/模式都适用）。如果当前任务不需要某个维度，就省略该 key。

示例：

```json
{
  "semantic_description": "Sums all elements of an integer array with one accumulator loop. The input array is read-only; the empty array returns 0.",
  "keywords": {
    "problem_kind": "sum",
    "data": "array",
    "pattern": "single_loop"
  }
}
```

## 8. 大模型查找流程

给定当前题目的四字段 fingerprint，大模型按下面顺序查找端到端样例：

1. 调用 `scripts/search_fingerprint.py` 生成相似样例路径列表，不要手动展开全量样例
2. 脚本只读取每个样例的四字段 fingerprint，不读取源码或 proof
3. 脚本按 keyword 匹配数排序：`problem_kind`、`data`、`pattern` 三项全中优先，其次两项命中
4. 脚本用 `semantic_description` 做轻量文本重合排序；大模型再对候选语义做最终判断，重点比较：
   - 输入输出关系是否相同
   - 是否修改内存
   - 循环 / 分支结构是否相同
   - 边界行为是否相同
5. 只展开最相关的少数样例，再读取其 `annotation_reasoning.md`、`proof_reasoning.md`、`issues.md` 和 `.v`
6. 复用 proof 前仍必须比较当前 VC 和旧 VC 主体；fingerprint 只能说明“相关”，不能证明 VC 相同

默认调用（同时检索 end-end + general 专题经验）：

```bash
python3 scripts/search_fingerprint.py --fingerprint output/verify_<timestamp>_<name>/logs/workspace_fingerprint.json
```

`--scope` 可限制范围：

- `--scope all`（默认）：同时检索 end-end 完整样例 + general 专题经验
- `--scope end-end`：只看完整 workspace 样例
- `--scope general`：只看 general 专题经验

输出（`--format paths`）：每行一个匹配路径。end-end 给 case dir，general 给 `<slug>.md` 路径。例如：

```text
experiences/end-end/array_sum
experiences/general/INV/1/array-dp-prefix-suffix.md
```

如果还没有 fingerprint 文件，直接传四字段：

```bash
python3 scripts/search_fingerprint.py \
  --problem-kind sum --data array --pattern single_loop \
  --semantic-description "Sums all elements of a read-only integer array."
```

## 9. 允许展开阅读的样例范围

- `experiences/end-end/` 下的样例可以直接展开阅读
- `experiences/general/<NAME>/<N>/<slug>.md` 是按 fingerprint 检索到的专题经验，命中即读
- 如果以上仍不够，再去 `QualifiedCProgramming/QCP_examples/` 下读取其他相关例子
- 仍然优先选择和当前目标最接近的题型、数据结构、witness 结构或 proof pattern
