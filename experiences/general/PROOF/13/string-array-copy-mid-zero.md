# 字符串/数组复制题如果只知道“当前位置读到 0”，先检查 contract 是否排除了中间 0

典型现象：

- `return_wit` 最后只剩：
  - `replace_Znth i 0 (l1 ++ d1) = l ++ [0]`
  - 或等价的 `CharArray.full ...` 目标
- 已知条件只有：
  - 前缀 `l1` 与 `l` 在 `< i` 上相等
  - `Znth i (l ++ [0]) = 0`
  - 长度关系

这时不要默认继续堆 tactic。

先判断当前 contract 是否真的能推出：

- `i = n`
- 或者 `l` 在 `0 <= k < n` 上都非零

如果都没有，那么 return witness 往往不是 proof 技巧问题，而是 specification 本身没有排除中间 `0`，导致“在第一个 `0` 处停止复制”不足以推出“整个目标数组等于 `l ++ [0]`”。

处理顺序：

1. 先用 `coqtop` 看清剩余目标是否已经退化成纯 list equality / `CharArray.full` equality
2. 如果是，就检查 precondition / ghost predicate 是否提供“唯一终止符”或“前缀元素非零”信息
3. 如果没有，优先记录为 contract gap，不要在 manual proof 里盲目硬证
