# 双分支区间收缩循环（二分查找类）优先用严格不等式作为 range-exclusion invariant（2026-05-25）

对使用 `left / right` 双指针的区间收缩循环（典型：`while (left <= right)` + 分支 `left = mid+1` / `right = mid-1` + 命中时立即返回），优先把两个 range-exclusion 事实写成**严格不等式**：

- `forall i, 0 <= i < left => l[i] < target`
- `forall i, right < i < n => target < l[i]`

**为什么用严格 `<` 而非 `!=`**：当 `a[mid] < target` 时，单调性给出 `l[k] <= l[mid] < target`，因此所有 `k <= mid` 都满足 `l[k] < target`；`a[mid] > target` 分支同理。`l[i] < target` 直接蕴含 `l[i] != target`，退出时无需额外改写；若只写 `!=`，保持性证明还需要额外的 case split 联系 `<` 与 `=`。

**变量边界**（必须覆盖 n=0 skip-loop 的初始状态）：

- `0 <= left && left <= n`（允许 `left == n` 表示"已超出右边界"）
- `-1 <= right && right < n`（允许 `right == -1` 表示空区间，对应 n=0 时 `right = n-1 = -1`）
- `left <= right + 1`（**不是** `left <= right`；允许空区间；退出条件 `left > right` 等价于 `left >= right + 1`，与此写法天然对应）

**退出状态**：`left > right` 结合两个 range-exclusion 事实，对任意 `k ∈ [0,n)`，要么 `k < left`（由第一条覆盖），要么 `right < k`（由第二条覆盖），直接推出 `forall k, l[k] != target`；无需额外 loop-exit assertion。

**不要**在 `return -1` 前加 loop-exit assertion：`mid` 在循环前声明、n=0 时未初始化；加了之后 symexec 会报 `Fail to Remove Memory Permission of mid`。
