# 字符串扫描类 return witness 常见的真正桥接点是先证 `i = n`

对 `string_copy`、`strlen` 这类题，`return_wit` 最后看起来常常像：

- `replace_Znth i 0 (...) = l ++ [0]`
- 或等价的 `CharArray.full ... |-- CharArray.full ...`

这时不要直接盯着最后一条 `replace_Znth`。

更稳的顺序是：

1. 先看当前假设能不能推出 `i = n`
2. 再用前缀相等性质证明 `l1 = l`
3. 最后再去化简 `replace_Znth` / `replace_nth`

如果一开始不先拿到 `i = n`，后面的尾部归一化通常会越写越乱。
