# 字符串扫描类题如果后条件要恢复整个字符串，前置条件必须能推出退出位置是最终 terminator

对这类程序：

- `strlen`
- `string_copy`
- 扫描到 `'\0'` 后返回、复制、计数、判断

Verify 阶段的 return witness 往往都会走到同一个桥接点：

- 先证明退出位置 `i` 就是最终 terminator 位置
- 再把“已处理前缀”恢复成完整字符串

如果 contract 不能推出这一点，proof 常见表现是：

- `symexec` 成功
- loop invariant 也能写出来
- 但 `return_wit` 最后只剩一条 `replace_Znth` / `CharArray.full` 的纯 list 目标，始终收不掉

因此，contract 设计时要先问：

1. 当前前置条件能否推出“遇到的第一个 `0` 就是最后一个 terminator”？
2. 如果后置条件要求完整恢复 `l ++ [0]`，是否已经显式排除了内部 `0`？

如果答案是否定的，就先改 contract，不要把这个缺口留给 Verify 阶段。
