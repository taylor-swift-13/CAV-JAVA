# Assertion Experience

本文件只记录 `annotated/verify_<timestamp>_<name>.c` 中 `Assert` / `which implies` / bridge assertion 的经验。

不记录：

- 循环 invariant 的整体设计（见 `INV.md`）
- symbolic 执行流程（见 `SYMEXEC.md`）
- manual proof（见 `PROOF.md`）


## 1. `Assert` 用来做阶段切换，不用来补救坏 invariant

`Assert` 最适合：

- 固定循环退出后的状态
- 调用子过程前整理资源
- 在高层语义和局部表示之间做桥接

如果你发现自己要靠很多 `Assert` 才能继续，优先回去改 invariant。

## 2. `which implies` 只做必要桥接

`which implies` 应该只承担：

- 当前证明工具需要的那一步显式过渡
- 从较强的局部信息过渡到下一条语句刚好可消费的形式

不要把大量推理都塞进 `which implies`。

## 3. bridge assertion 要贴着下一条语句写

桥接断言应直接服务于下一步：

- 下一条是数组读写，就桥到对应 segment/full 形状
- 下一条是结构字段读写，就桥到对应展开层级
- 下一条是函数调用，就桥到被调函数前置条件

不要提前写很远之后才用到的 assertion。

## 4. 循环退出后通常需要一个显式退出断言

常见用途：

- 固定 `i == n`
- 固定 `j + 1 == bound`
- 把“未进入下一轮”转成后置条件所需边界

很多 `return_wit` 卡住，本质是少了一条退出后的 `Assert`。

但要注意：

- 退出断言必须贴着真正的循环退出点写
- 不要把它放到函数即将返回、局部变量准备销毁的位置去强行替换状态

典型错误现象：

- `Fail to Remove Memory Permission of i`

这通常不是“退出条件不对”，而是断言放得太晚，破坏了局部变量清理流程。

更稳的处理方法：

- 优先依赖循环 invariant 自然导出的退出状态
- 只有确实需要固定纯条件时，才补最小的 loop-exit assertion
- 如果加了退出断言反而让 `symexec` 卡在 local permission，先删掉它再重跑

## 5. 参数不变关系常常要显式桥出来

如果后面需要从当前状态回到 `@pre` 版本，通常要在注释里显式保留：

- `a == a@pre`
- `out == out@pre`
- `n == n@pre`

不要指望这些关系总能自动恢复出来。

## 6. `which implies` 不要承担“大段证明”

如果你发现 `which implies` 里需要表达很多层：

- 结构重组
- 多个纯命题联立
- 前后缀语义重建

通常说明问题不在 `which implies`，而在于：

- invariant 太弱
- 上一个 `Assert` 位置不对
- 抽象谓词展开层次不对

处理顺序应该是：

1. 先减小 `which implies` 负担
2. 回去补 invariant 或调整 bridge assert
3. 再重新 `symexec`

## 7. 多分支分类关系优先拆成多条单一 implication

如果数组元素的语义是三路或更多分类，例如：

- `x > 0` 时结果为某个值
- `x < 0` 时结果为某个值
- `x == 0` 时结果为某个值

不要在 invariant / assert 里写成包含 `||` 的多 case 断言；前端可能报 `Multiple cases inside pre- or post-condition`。

也不要优先把多条 implication 塞进同一个大 consequent，例如：

- `(range) => ((case1 => value1) && (case2 => value2) && (case3 => value3))`

更稳的写法是拆成多条独立事实：

- `(range && case1) => value1`
- `(range && case2) => value2`
- `(range && case3) => value3`

这样通常能避免 disjunction 被拒绝，也能减少单个纯命题里的 clause 爆炸。

## 9. bridge Assert 是语义切点：必须包含后续语句需要的所有上下文（2026-05-25）

`Assert` 对 `symexec` 相当于一个"重置点"：Assert 之后的一切只能使用 Assert 中明确写出的事实；Assert 之前上下文中未被包含的内容会被截断丢失。

**常见后果**：如果 bridge Assert 只写了新推出的事实（例如只写 `0 <= mid && mid < n && left <= mid && mid <= right`），而省略了循环 invariant 中的 `target == target@pre`，那么紧接在 Assert 之后的 `a[mid] == target` 比较就没有 `target` 可用，witness 会缺失这个纯事实，或产生意外的 `target_pre` / `target` 不匹配。

**实操规则**：

- bridge Assert 的内容 = 完整循环 invariant（原样复制）+ 新推出的额外事实（例如 mid 的范围、bridge 目标）
- 不要只写新推出的事实
- 不要把 invariant 中"感觉这里用不到"的部分省略
- 唯一可以安全省略的是：确定在 Assert 之后到下一个语义切点之前**绝对不再需要**的事实

## 8. C `int` 形参的范围事实优先用 `by local` 从局部 store 提取

如果前置条件没有显式写 `x <= INT_MAX`，但当前程序点仍然持有 `x` 的 `Int` 局部变量 store，不要先写普通纯断言：

```c
/*@ Assert
      x@pre <= INT_MAX
*/
```

这种断言可能生成错误形状的纯 VC，要求从 formal `Require` 直接证明 `x@pre <= INT_MAX`。

更稳的做法是在局部变量还没有被抽象掉、且当前 `x` 仍等于需要保存的值时，贴着控制点写：

```c
/*@ x <= INT_MAX by local */
```

然后在后续 invariant 中携带需要的 `x@pre <= INT_MAX` 或对应上界。这样生成的 witness 左侧会保留 `(( &( "x" ) )) # Int |-> x_pre` 这类局部 store，自动证明可以从 C `int` 表示性中提取上界，而不是把它误变成 `Require` 必须提供的纯事实。
