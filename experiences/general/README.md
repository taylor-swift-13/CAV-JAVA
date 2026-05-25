# Readme Experience

本目录是经验入口。

## 1. Contract 入口

- `CONTRACT.md`
- `EVAL.md`

## 2. Verify 入口

- `SYMEXEC.md`
- `ASSERTION.md`
- `INV.md`
- `PROOF.md`
- `COMPILE.md`
- `AUDIT.md`

## 3. 更新规则

- 只写可复用结论
- 不写单题一次性细节
- 对已有规则做更正时，直接改原条目

## 4. 按症状检索

遇到问题时优先按症状跳转，不要从头通读所有文档。

- 自动 verify / Codex 进程卡住、stdout/stderr 不再增长：看 `SYMEXEC.md` 1
- 改了 annotation 后是否要重新生成 Coq：看 `SYMEXEC.md` 2
- `symexec` 失败且怀疑注释控制点错位：看 `SYMEXEC.md` 3
- `symexec` 成功但剩纯 list / arithmetic witness：看 `SYMEXEC.md` 4、13
- invariant 不知道怎么设计：看 `INV.md` 1、3、5、7
- 扫描类循环：看 `INV.md` 4
- nested loop：看 `INV.md` 8
- 参数未变关系污染 return witness：看 `INV.md` 9、`ASSERTION.md` 5、`PROOF.md` 16
- 数组逐步写入 / DP 数组：看 `INV.md` 10
- merge / 双指针归并：看 `INV.md` 11、12 和 `PROOF.md` 21
- 排序前缀 / insertion sort：看 `INV.md` 13、15 和 `PROOF.md` 31、32
- `for` 循环初始化边界和 skip-loop：看 `INV.md` 14
- contract 是否真的刻画实现、eval case 怎么选：看 `EVAL.md` 1、2、3
- 需要 loop-exit assertion：看 `ASSERTION.md` 4
- 多分支 implication 太复杂：看 `ASSERTION.md` 7
- proof 编译失败但只看到一行报错：看 `PROOF.md` 5
- witness 太复杂、主证明硬顶 tactic：看 `PROOF.md` 7
- `Cannot find witness`：看 `PROOF.md` 8、19
- helper lemma 参数被 Coq 猜错：看 `PROOF.md` 20
- QCP assertion 的 disjunction / existential：看 `PROOF.md` 22
- 复制相似 witness 后 hypothesis 编号错：看 `PROOF.md` 23
- return witness 要把 prefix/suffix 归一化：看 `PROOF.md` 24
- `replace_Znth` / `replace_nth` 卡住：看 `PROOF.md` 25
- 局部变量从有值态变未定义态：看 `PROOF.md` 26
- `entailer!` 后 bullet 顺序不对：看 `PROOF.md` 27
- 溢出 witness 缺 `Int` 范围：看 `PROOF.md` 28
- `Local Open Scope sac` 影响 list 语法：看 `PROOF.md` 29
- Coq load-path / 编译顺序 / `goal_check`：看 `COMPILE.md` 2、5、8、9
- audit / 反作弊 / compile replay：看 `AUDIT.md` 1、2、3
