# max/min 扫描题的 helper lemma 值得模板化

对 max/min 扫描类题目，反复会用到这些 lemma：

- 前缀中任意元素都不超过当前 prefix max
- 如果所有元素都不超过某个上界，则 prefix max 也不超过这个上界
- 在列表尾部追加一个元素后，max/min 的单调性
- 追加元素不改变当前 max/min 的条件

这类题的主 witness 通常不难，难点在这些纯 list helper lemma。

所以更稳的策略是：

- 尽早把它们沉淀成局部模板
- 主 witness 只做“把循环状态翻译成 prefix 语义，再调用 lemma”

不要每道 max/min 扫描题都从零在主 witness 里手搓同一套推理。
