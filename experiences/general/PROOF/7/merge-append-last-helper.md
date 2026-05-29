# merge / two-pointer proof 要先抽 append-last helper，不要在 witness 里展开递归硬证

`merge_sorted_arrays` 的核心 proof 难点不是 separation logic，而是纯 list 语义：

- 写 `a[i]` 后，要证明新输出前缀等于 `merge(sublist 0 (i+1) a, sublist 0 j b)`
- 写 `b[j]` 后，要证明新输出前缀等于 `merge(sublist 0 i a, sublist 0 (j+1) b)`

如果在主 witness 里直接展开 `merge` 递归，proof 会迅速失控。

更稳的做法是先在 `proof_manual.v` 中抽 helper lemma：

- `replace_Znth_app_suffix_head_Z`：把 `replace_Znth k x (prefix ++ sublist k n old)` 归一化成 `(prefix ++ [x]) ++ sublist (k+1) n old`
- `sublist_prefix_snoc_Z`：把 `sublist 0 (i+1) l` 归一化成 `sublist 0 i l ++ [Znth i l 0]`
- `merge_app_a_last`：当所有已消费 `a` 都 `<= x` 且所有已消费 `b` 都 `< x` 时，`merge(a ++ [x], b) = merge(a, b) ++ [x]`
- `merge_app_b_last`：当所有已消费 `a` 都 `<= y` 且所有已消费 `b` 都 `<= y` 时，`merge(a, b ++ [y]) = merge(a, b) ++ [y]`

主 witness 应只做：

- 建立当前 snoc 形式
- 从 invariant 的跨边界关系推出 helper lemma 的 `Forall` 条件
- 调用 helper lemma 改写语义等式
- 交给 `entailer!` 和 `lia` 处理剩余 shape / arithmetic

这个模式适用于 merge、partition、two-sorted-array scan、双指针输出数组等题。
