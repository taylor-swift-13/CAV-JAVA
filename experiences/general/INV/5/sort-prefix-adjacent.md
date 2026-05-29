# 排序前缀 invariant 可优先携带相邻有序关系

对插入排序这类每轮只在局部移动元素、最终需要 `sorted_z` 的数组排序题，循环 invariant 里直接携带 `sorted_z(sublist 0 i l)` 可能让最终插入/交换 witness 变成大段结构化 list proof。

更稳的做法是携带等价但更局部的相邻有序关系：

- `forall k, 0 <= k && k + 1 < i => l[k] <= l[k + 1]`

这样保持性只需按受影响的相邻边分类讨论，未受影响的边直接复用旧 invariant；退出时再用一个 Coq helper 从相邻有序关系和长度推出 `sorted_z`。这通常比在每个循环保持 witness 中直接证明 `sorted_z` 的 `sublist` / `replace_Znth` 结构变换更稳定。
