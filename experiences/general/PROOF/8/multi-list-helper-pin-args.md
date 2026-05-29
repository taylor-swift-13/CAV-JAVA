# 多个相似逻辑列表同场时，helper lemma 参数必须显式钉住

在嵌套循环或“保存旧状态 + 当前状态”的 proof 里，经常同时出现：

- 外层循环保存的整体列表
- 内层循环的 base 列表
- 当前 heap 表示列表
- 写入后的候选列表

这时调用局部 helper lemma 不要只写少量索引参数再交给 `eauto` 猜列表参数。即使目标看起来唯一，Coq 也可能把 helper 的 `l_base` 实例化成外层旧列表，留下一个形如“当前 heap list 等于用旧列表拼出来的 sublist 结构”的不可证 side condition。

更稳的写法是：

- 在 `eapply ... with` 中显式给出所有关键列表参数，例如 `(l_base := l_base) (l_cur := l_cur)`
- 对结构等式 side condition 直接 `exact Hshape`
- 对长度等式直接 `exact Hlen` 或 `symmetry; exact Hlen`
- 避免在这种 helper 调用后使用过宽的 `try eauto; try (symmetry; exact H...)`

这类问题的典型症状不是核心语义 lemma 错，而是 `Qed` 报 `Attempt to save an incomplete proof`，`Show` 后剩余目标里出现了错误版本的 sublist 结构。
