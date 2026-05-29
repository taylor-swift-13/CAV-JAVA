# safeExec / refinement VC 先分离空间侧，再规范化执行侧

如果目标涉及 `safeExec`、refinement 或 monadic execution predicate，优先按固定 proof skeleton 处理。

稳定顺序：

1. `pre_process.`
2. 先选择必要 `Exists`。
3. 使用 `split_pure_spatial` 分离空间侧和执行侧。
4. 先证明空间侧。
5. 执行侧只在对应 hypothesis 中展开 wrapper。
6. 每次 `unfold ... in H at 1` 或 `unfold_loop in H` 后都运行 `prog_nf in H`。
7. 分支目标用 `safe_choice_l H` 或 `safe_choice_r H` 选择匹配分支。
8. normalized hypothesis 和目标一致时用 `exact H` 收尾。

禁用模式：

- 不要在 `split_pure_spatial` 前展开 `safeExec` 相关定义
- 不要 `unfold ... in *`
- 不要手写 `assert (Hs : safeExec ...)`
- 不要用 `safeExec_bind_reta` / `safeExec_bind` 手工重建执行谓词；优先用 `prog_nf`
