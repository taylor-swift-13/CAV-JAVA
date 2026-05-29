# insertion sort 的 sorted proof 优先先证 adjacent order，再在 return 处转成 `sorted_z`

如果 invariant 直接维护 `sorted_z(sublist 0 i l)`，最终插入时通常需要证明 `replace_Znth` 后的结构化 list 仍满足 `sorted_z`，这会牵涉大量 `sublist` 和结构归纳。

更稳定的证明路线是：

1. annotation 层维护相邻有序关系。
2. final insertion witness 只证明相邻有序关系保持。
3. return witness 中一次性调用 helper，把“全数组相邻有序 + 长度覆盖”转成 `sorted_z l`。

这个分层的好处是：

- 循环保持性只需处理局部相邻边
- 未受影响的相邻边可以直接复用 invariant
- `sorted_z` 的结构归纳集中在一个 return helper 中
- witness 里的 list 结构改写明显减少
