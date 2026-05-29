# return witness 优先做 full-prefix 和 empty-suffix 归一化

对逐步写满输出数组的题，最终 return witness 往往不是新的语义问题，而是需要把 loop state 归一化成后条件形状。

稳定顺序：

1. 从退出条件推出所有索引到达边界，例如 `i = n`、`j = m`。
2. 推出写入长度到达整段，例如 `k = n + m`。
3. 用 `sublist_self` 把 `sublist 0 n a` 改成 `a`。
4. 用 `sublist_self` 把 `sublist 0 m b` 改成 `b`。
5. 用 `sublist_nil` 把输出未写后缀改成 `nil`。
6. 用 `app_nil_r` 把 heap shape 改成完整输出。
7. 最后用 invariant 保存的 semantic equality 替换 `lout_done`。

不要一开始就证明最终数组相等；先把 prefix/suffix shape 化简到和后条件同形，`entailer!` 才容易收掉。
