# `replace_Znth` 最后一步经常卡在 `nat` 索引没有化简

即使在 `Z` 上已经知道索引等于 `0`，展开

- `replace_Znth`

之后，Coq 里常常还残着：

- `replace_nth (Z.to_nat (...)) ...`

如果这个 `Z.to_nat (...)` 不显式改成 `0%nat`，`simpl` 很可能不会继续。

稳定写法是：

1. `unfold replace_Znth`
2. 显式把 `Z.to_nat (...)` 改成 `0%nat`
3. 再 `simpl`

很多看起来像“最后一条列表相等还差一点”的目标，真正缺的就是这一步。
