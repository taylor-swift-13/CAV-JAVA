# Eval Experience

本文件只记录 eval 阶段的通用经验：如何用具体 case 检查 contract 是否真正刻画了
实现行为。它不记录 verify 的 annotation / proof 技巧，也不记录 audit 的反作弊
结论。

## 1. 覆盖所有控制分支

如果正例没有覆盖所有实现分支，eval 很容易把单分支 spec bug 漏掉。生成 case 时，
先按控制流或输入分区划分，再为每个分区至少放一个正例。

## 2. 负例要针对具体子句

负例不要只写“这是错的”。必须明确它违反的是哪条 `Require` 或 `Ensure` 子句，
这样后面的 `evaluation.json` 才能把失败定位到具体 contract 语义。

## 3. 不可判定时要诚实给 `Inconclusive`

如果某条 contract 依赖外部 Coq 谓词、抽象关系或当前 case 无法机械判断的语义，
不能硬判 `Correct`。应把该 case 标成 `needs_judge`，仍无法确定时给
`Spec verdict: Inconclusive`。
