# listlib Section 参数导出后的引理参数顺序

listlib 中多个引理定义在 `Section Index` 中，Section 头声明 `Context {A: Type} (d: A)` 其中 `d` 是默认值。Section 关闭后，`d` 成为这些引理的 **第一个显式参数**（若引理的语句或证明中使用了 `d`）。参数顺序如下：

| 引理 | Section 内签名 | 关闭后实际签名（常用显式参数） |
|---|---|---|
| `sublist_single` | `n l` (+ proof) | `d n l` (+ proof) |
| `Znth_cons` | `n a l` (+ proof) | `d n a l` (+ proof) |
| `replace_nth` | `n l a` | `n l a`（*注意：list 是第二参数，value 是第三参数*） |

**关键规则**：
- `sublist_single 0 n l` — 正确；`sublist_single n l 0` — 错误（0 会被当作 d，n 被当作 n，l 被当作 proof → type error）
- `Znth_cons 0 n a l` — 正确；`Znth_cons n a l 0` — 错误（同理）
- `replace_nth i l v` — 正确（list 在前，value 在后）；`replace_nth i v l` — 错误，会产生类型推断错误

**Z 版 vs nat 版**：
- `Zsublist_nil l a b` — Z 索引的 `sublist a b l = []`（来自 Positional.v）
- `sublist_nil l a b` — nat 索引的 `Nsublist a b l = []`（来自 Length.v）
- 在 `proof_manual.v` 中应使用 `Zsublist_nil`，不要用 `sublist_nil`

**验证方式**：若 rewrite 报 "term X has type list T while expected to have type Z/nat"，基本确认是参数顺序写错了。

**注意**：旧 experience 的 proof_manual.v 可能含有这些错误的调用；复用时需要检查并修正。当前 `end-end/insertion_sort/coq/generated/insertion_sort_proof_manual.v` 已按正确参数顺序更新（2026-05-26）。
