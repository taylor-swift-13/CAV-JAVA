# 双指针归并类题不能只记录「已合并前缀」，还要记录跨边界顺序历史

`merge_sorted_arrays` 这类题难的根本原因是：程序每轮只比较当前 `a[i]` 和 `b[j]`，但 proof 里要证明「把当前元素追加到已合并结果末尾」是合法的。

只写下面这些信息通常不够：

- `0 <= i <= n`
- `0 <= j <= m`
- `k == i + j`
- `lout_done == merge(sublist(0, i, a), sublist(0, j, b))`

因为当选择 `a[i]` 时，证明需要知道所有已经消费的 `b[0..j)` 都小于当前和未来相关的 `a`；当选择 `b[j]` 时，也需要知道已经消费的 `a[0..i)` 都不大于当前和未来相关的 `b`。

更稳的 invariant 要把两类历史关系显式留下来：

- consumed `b` 与 future `a` 的严格顺序关系
- consumed `a` 与 future `b` 的非严格顺序关系

这两个关系不是装饰性信息，而是证明 merge-prefix 语义保持性的核心桥梁。没有它们，`symexec` 可能仍能生成 VC，但 manual proof 会在 `lout_done ++ [x] = merge(...)` 这类纯 list 目标上卡死。

设计这类 invariant 时建议先用自然语言写清楚：

- `lout_done` 精确等于哪两个已消费前缀的 merge
- `out` 的 heap shape 是 `app(lout_done, sublist(k, n + m, old_out))`
- `k` 是否始终等于 `i + j`
- 两个输入数组是否保持原始长度和值
- tie rule 是选择 `a` 还是选择 `b`，跨边界关系必须和 tie rule 一致

尤其要注意 `<=` 和 `<` 的方向：如果代码在 `a[i] <= b[j]` 时选择 `a`，那么 consumed `a` 到 future `b` 可以是 `<=`，而 consumed `b` 到 future `a` 往往需要 `<`，否则 append-last helper lemma 的条件会对不上。
