# 整数除以 2 的截断商需要局部 helper lemma（2026-05-25）

对使用 `mid = left + (right - left) / 2` 的程序，生成的 `safety_wit` 目标通常形如：

```
INT_MIN <= left + (right - left) ÷ 2 && left + (right - left) ÷ 2 <= INT_MAX
```

标准 `entailer!` 不能自动推出 `0 <= (right - left) ÷ 2 <= right - left`（Coq 的截断除法 `Z.quot`），需要先在 `proof_manual.v` 中定义局部 helper lemma：

```coq
Lemma binary_search_quot2_bounds: forall x, 0 <= x -> 0 <= x ÷ 2 <= x.
Proof. intros; split; [apply Z.quot_nonneg | apply Z.quot_le_upper_bound]; lia. Qed.
```

然后在 `safety_wit_4` 证明中按固定顺序：

```coq
prop_apply (store_int_range (&("left")) left).
prop_apply (store_int_range (&("right")) right).
apply binary_search_quot2_bounds; lia.
entailer!.
```

此 helper 适用于所有 `0 <= x` 时的 `x ÷ 2` 上下界证明，不局限于 binary search；其他需要证明截断商范围的题可以直接复用。
