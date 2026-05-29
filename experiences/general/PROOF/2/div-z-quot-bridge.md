# 规格递归用 `Z.div`、生成 C 目标用 `Z.quot` 时，先桥接非负除法

数字循环里，Coq 规格可能写成：

```coq
digit_sum_fuel (Z.div n 10) k
```

而 C 表达式生成的目标通常使用 `n ÷ 10`。在 `0 <= n` 且除数为正时，先用 `Z.quot_div_nonneg` 建立二者相等，不要在主 witness 里反复硬改。

推荐拆法：

- 规格 fuel-stability 递归跟随规格本身，使用 `n / 10`
- C 循环保持性和安全性使用生成目标里的 `n ÷ 10`
- 单步语义 lemma 的最后用 `Z.quot_div_nonneg` 把 `n / 10` 替换成 `n ÷ 10`

注意 `replace` 的方向：`replace (n ÷ 10) with (n / 10)` 和 `replace (n / 10) with (n ÷ 10)` 生成的等式方向相反；一个可能需要 `symmetry`，另一个不需要。以当前 Coq 报错里的目标等式为准。
