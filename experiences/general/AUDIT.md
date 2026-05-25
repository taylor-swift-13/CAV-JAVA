# Audit Experience

本文件只记录 audit 阶段的通用经验：如何判断一个 QCP proof 是否可信，如何识别
反作弊或伪证明。它不记录 contract 写法，也不记录具体 witness 证明技巧。

## 1. 只有 `proof_manual.v` 里的 stub 才算作弊

`proof_manual.v` 中留下 `Admitted.`、手写 `Axiom`、`Parameter`、`Abort`，都应视为
高优先级风险。verify 的人工证明责任就在这个文件里，stub 会直接让“证明成功”
失去意义。

反过来，`proof_auto.v` **全是 `Proof. Admitted.`（包括 `safety_wit` / `return_wit`
/ `partial_solve_wit`）是 symexec 生成的正常形态，不是作弊、不要报**。所有
`experiences/end-end/` 参考解的 `proof_auto.v` 都是 0 个 `Qed`、全 `Admitted`；
真正的证明负担只在 `proof_manual.v` 的 `entail_wit`（必须 `Qed`）。

因此**不要**用 `Print Assumptions` 把 `proof_auto.v` 的义务报成 axiom 来判
`NotVerified`——那会把这个被接受的约定当成不健全，错杀合格的 verify 结果。

## 2. compile replay 必须重放

audit 不能只信已有日志。至少要重放一次 `goal` / `proof_auto` / `proof_manual` /
`goal_check` 的编译链；如果重放失败，即使之前某次日志写着成功，也应判为
`NotVerified`。

## 3. contract 变弱要按语义审查

只要 verified 版本删掉、改弱或绕开了 original contract 的关键约束，就应该进入
审计发现。格式不同不一定是问题，但语义变弱必须被当成 error 处理。
