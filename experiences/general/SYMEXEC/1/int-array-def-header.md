# `int_array_def.h` 是不应该放进 annotated C 的头文件

如果 `input/<name>.c` 包含 `#include "../../int_array_def.h"`（或其他路径的 `int_array_def.h`），在 `annotated/` 工作副本里必须删掉这行。

原因：
- `int_array_def.h` 是给 C 编译器用的 C-level 定义（不是标准库头文件）
- `symexec` 的 include search path 找不到这个文件，无论设置哪个 `-slp` 或 include 路径
- `IntArray::full`、`IntArray::missing_i` 等 separation logic 谓词是 symexec 内置的，通过 `load_builtin_int_array_strategy_lib` 加载，不需要任何头文件声明

操作：
1. 在 `annotated/verify_<timestamp>_<name>.c` 里删掉 `#include "../../int_array_def.h"` 这一行
2. 保留 `verification_stdlib.h` 和 `verification_list.h` 的 include（改成不带 `../../` 的 bare 名字即可）
3. 重新跑 `symexec`

不要尝试：修改 `-slp` 路径、设置 `INCLUDE_PATH` 环境变量、在 QCP 目录下创建 symlink 等——这些均无效。
