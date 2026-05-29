# `symexec` 成功后如果 witness 是 merge/list 语义，不要误判为 annotation 失败

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
