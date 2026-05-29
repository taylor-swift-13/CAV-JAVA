# 溢出 witness 不要只看纯前提，先从栈槽取回 `Int` 范围

如果 `safety_wit` 的目标是类似 `cnt + 1 <= INT_MAX`，而 `pre_process; entailer!` 后纯上下文里没有 `n <= INT_MAX`，不要马上判断为 contract gap。

先在 `entailer!` 之前对相关栈变量使用：

```coq
sep_apply store_int_range.
```

它可以从空间断言 `(&( "n")) # Int |-> n_pre`、`(&( "i")) # Int |-> i` 这类栈槽中恢复 `Int.min_signed <= ... <= Int.max_signed`。之后再结合循环计数的纯上界，例如 prefix count `<= i - 1` 和 `i < n_pre`，通常可以完成自增溢出证明。
