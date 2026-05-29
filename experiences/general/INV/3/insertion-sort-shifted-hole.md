# 插入排序内循环优先建模成 shifted-hole

插入排序内循环不是普通交换排序，它的核心状态是"拿出 `key` 后，右移元素形成一个 hole"。

更稳的 inner invariant 应显式保存：

- `l_base`：进入本轮外循环时的基准数组
- `l_cur`：当前 heap 数组
- `key`：被拿出的元素
- `j` 和 `i` 对应的 hole 位置
- `l_cur` 与 `l_base` 的 shifted-hole 结构关系

典型结构是：

- 前缀未受影响：`sublist 0 (j + 2) l_base`
- 被右移区间：`sublist (j + 1) i l_base`
- 后缀未受影响：`sublist (i + 1) n l_base`

这比只写"当前前缀仍有序"更适合证明：

- 一次右移后 heap shape 怎么变化
- `Znth j l_cur` 和 `Znth j l_base` 如何对应
- 最终 `a[j + 1] = key` 后如何恢复完整数组
- permutation 如何从局部插入结构推出

如果 invariant 没有显式保存 shifted-hole，final insertion witness 往往会退化成很难控制的 `replace_Znth` / `sublist` 大等式。
