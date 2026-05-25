# String And Char Array Predicates

## 头文件

```c
#include "char_array_def.h"
```

## 常用谓词

| 谓词 | 作用 | 何时用 |
| --- | --- | --- |
| `CharArray::full(a, n, l)` | 长度为 `n` 的字符数组内容是 `l` | 普通 `char` 缓冲区 |
| `CharArray::seg(a, lo, hi, l)` | `[lo, hi)` 的字符数组段 | 前后缀、字符串扫描 |
| `CharArray::missing_i(a, i, lo, hi, l)` | 打开第 `i` 个字符槽位 | 读取或更新 `a[i]` |
| `CharArray::undef_full(a, n)` | 整个缓冲区已分配未初始化 | 初始化字符数组 |
| `CharArray::undef_seg(a, lo, hi)` | 子段未初始化 | 逐步填充 |

辅助函数：

- `repeat_Z(c, n)`
- `replace_Znth(i, c, l)`
- `Znth(i, l, default)`

## C 字符串的标准表示

仓库里最常见的字符串断言不是“只存 `n` 个字符”，而是“额外带一个 `0` 终止符”：

```c
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

这表示：

- `l` 是实际字符串内容
- 数组总长度是 `n + 1`
- 最后一个字节是 `'\0'`

直接参考：

- `QualifiedCProgramming/QCP_examples/kmp_rel.c`

如果后续函数语义依赖“扫描到第一个 `'\0'` 就停止”，并且规格要把整个字符串内容恢复成完整的 `l ++ [0]`，那么上面这条断言通常还不够。

这时还需要显式补：

```c
(forall (k: Z), (0 <= k && k < n) => l[k] != 0)
```

这条条件表示：

- `l` 的前 `n` 个字符里没有内部 `0`
- 唯一的 terminator 在最后那个额外位置

否则 `CharArray::full(s, n + 1, app(l, cons(0, nil)))` 只说明“最后还有一个 `0`”，并不排除中间更早出现 `0`。

## 最常抄的模板

### 1. 初始化字符缓冲区

```c
/*@ Require 0 <= n && CharArray::undef_full(a, n)
    Ensure CharArray::full(a, n, repeat_Z(m, n))
*/
```

循环不变量常写成：

```c
/*@ Inv
    0 <= i && i <= n@pre &&
    CharArray::full(a@pre, i, repeat_Z(m@pre, i)) *
    CharArray::undef_seg(a@pre, i, n@pre)
*/
```

代表例子：

- `QualifiedCProgramming/QCP_examples/chars.c`

### 2. 只读字符串

```c
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil))) &&
            (forall (k: Z), (0 <= k && k < n) => l[k] != 0)
    Ensure CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

适合 `strlen`、扫描、匹配等函数。代表例子：

- `QualifiedCProgramming/QCP_examples/kmp_rel.c`

### 3. 打开一个字符位置

和整数数组完全同构。读 `a[i]` 或写 `a[i]` 时，可以用：

```c
/*@ CharArray::full(a, n, l)
    which implies
    data_at(a + (i * sizeof(char)), char, l[i]) *
    CharArray::missing_i(a, i, 0, n, l)
*/
```

写回后再折回 `CharArray::full(...)` 或 `replace_Znth(...)` 版本。

## 字符串题的两个惯用套路

### 模式一：字符串不变，辅助数组变化

KMP 里常见：

```c
CharArray::full(patn, n + 1, app(patn0, cons(0, nil))) *
IntArray::full(vnext, n, vnext0)
```

也就是：

- 字符串保持只读
- prefix table 或索引数组单独建模

### 模式二：用 `strlen` 规格把长度逻辑化

仓库里 `strlen` 的规格就是：

```c
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

所以后续证明常用“调用 `strlen` 把 `n` 从字符串内容中抽出来”。

## 常见坑

- 证明字符串函数时，别忘了终止符，占的是 `n + 1`。
- 如果后条件要求恢复整个 `l ++ [0]`，不要漏掉“前缀无内部 `0`”这条条件。
- `char` 数组初始化常从 `undef_full` 开始，不要直接假设 `full`。
- 如果题目只扫描但不修改字符串，保持 `CharArray::full` 不变最省事。
