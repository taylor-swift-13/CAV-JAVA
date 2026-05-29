# insertion final witness 要拆成 shape / permutation / order / length 四类 helper

插入排序最后一步 `a[j + 1] = key` 的 witness 容易看起来像一个整体目标：

- 写入后的数组是某个 `replace_Znth`
- 新前缀有序
- 新数组是旧数组的 permutation
- 长度和 heap shape 保持

不要在主 witness 里同时展开这些性质。更稳的拆法是四类 helper：

- shape helper：把 `replace_Znth (j + 1) key l_cur` 改写成 `sublist 0 (j + 1) l_base ++ key :: nil ++ sublist (j + 1) i l_base ++ sublist (i + 1) n l_base`
- permutation helper：只证明 final inserted list 与 `l_base` permutation
- adjacent-order helper：只证明插入后前缀的相邻有序关系，按受影响边界分类讨论
- length helper：只证明 final inserted list 的 `Zlength`

主 witness 只负责：

- `Exists (replace_Znth (j + 1) key l_cur)`
- 用 shape helper 统一 list 表达
- 分别调用 permutation / adjacent-order / length helper
- 处理局部变量权限和简单算术

这样每个 helper 的失败点都很明确，也避免在一个 bullet 中同时面对 `replace_Znth`、`sublist`、`Permutation` 和 `sorted_z`。
