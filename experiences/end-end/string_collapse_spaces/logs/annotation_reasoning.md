## 2026-04-22 annotation round 1

Current program point: the only loop is the `while (1)` beginning after initialization:

```c
int i = 0;
int j = 0;
int in_space = 0;

while (1) {
    if (s[i] == 0) {
        break;
    }
    ...
    i++;
}

out[j] = 0;
```

Without an invariant, `symexec` will not have the loop summary needed to preserve the input buffer, describe the partially written output buffer, or connect the two integer indices to the Coq specification. The postcondition needs the input buffer unchanged and the output buffer to contain `string_collapse_spaces_spec(l)` followed by a null byte and an arbitrary suffix. The loop body scans one input cell per iteration (`i` is the number of processed input characters) and writes zero or one output character (`j` is the length of the collapsed output for the processed prefix).

The planned invariant is attached immediately before `while (1)` and uses an existential logical list `lout` for the current contents of the whole output buffer:

```c
/*@ Inv exists lout,
      0 <= i && i <= n@pre &&
      0 <= j && j <= i &&
      (in_space == 0 || in_space == 1) &&
      s == s@pre &&
      out == out@pre &&
      n == n@pre &&
      Zlength(l) == n@pre &&
      Zlength(d) == n@pre + 1 &&
      Zlength(lout) == n@pre + 1 &&
      j == Zlength(string_collapse_spaces_spec(sublist(0, i, l))) &&
      (forall (p: Z),
        (0 <= p && p < j) =>
        lout[p] == string_collapse_spaces_spec(sublist(0, i, l))[p]) &&
      (forall (p: Z),
        (j <= p && p < n@pre + 1) =>
        lout[p] == d[p]) &&
      (in_space == 0 => (i == 0 || l[i - 1] != 32)) &&
      (in_space == 1 => (0 < i && l[i - 1] == 32)) &&
      (forall (k: Z), (0 <= k && k < n@pre) => l[k] != 0) &&
      CharArray::full(s, n@pre + 1, app(l, cons(0, nil))) *
      CharArray::full(out, n@pre + 1, lout)
*/
```

Initialization should hold with `i = 0`, `j = 0`, `in_space = 0`, and `lout = d`: the processed prefix is `sublist(0,0,l)`, whose collapsed result has length zero, and no output cells have been changed. The suffix fact covers all output cells because `j == 0`.

Preservation follows the three code cases. If `s[i] == 0`, the loop exits and does not need to re-establish the invariant. If `s[i] == 32` and `in_space == 0`, the program writes one space at `out[j]`, increments `j`, sets `in_space = 1`, and then increments `i`; this matches extending the processed prefix by the first space of a run. If `s[i] == 32` and `in_space == 1`, the program skips the write, keeps `j`, and only advances `i`; this matches suppressing an additional space in an existing run. If `s[i] != 32`, the program writes the character, increments `j`, sets `in_space = 0`, and advances `i`; this matches appending a non-space character to the collapsed prefix.

The invariant includes the simple `in_space` characterization using the previous input character. This is the local fact needed to distinguish the first space in a run from later spaces without changing the formal contract. It also keeps `s`, `out`, and `n` equal to their pre-state values, because the Ensure clause is expressed using `n@pre` and unchanged buffers.

After the loop breaks, the program has just observed `s[i] == 0`. Together with the invariant and the precondition fact that no `l[k]` for `0 <= k < n` is zero, this should imply `i == n@pre`; otherwise `s[i]` would be a nonzero element of `l`. I will add a loop-exit `Assert` before `out[j] = 0` to fix the state consumed by the final store:

```c
/*@ Assert exists lout,
      i == n@pre &&
      0 <= j && j <= n@pre &&
      s == s@pre &&
      out == out@pre &&
      n == n@pre &&
      Zlength(l) == n@pre &&
      Zlength(d) == n@pre + 1 &&
      Zlength(lout) == n@pre + 1 &&
      j == Zlength(string_collapse_spaces_spec(l)) &&
      (forall (p: Z),
        (0 <= p && p < j) =>
        lout[p] == string_collapse_spaces_spec(l)[p]) &&
      (forall (p: Z),
        (j <= p && p < n@pre + 1) =>
        lout[p] == d[p]) &&
      CharArray::full(s, n@pre + 1, app(l, cons(0, nil))) *
      CharArray::full(out, n@pre + 1, lout)
*/
```

This assertion is placed before the final output write while local permissions are still available. It should make the final null terminator store produce the exact postcondition shape: the output prefix is the full collapsed string, position `j` becomes `0`, and the remaining suffix can instantiate the existential `t` with the tail of the old output list after index `j`.

## 2026-04-22 annotation round 2

The first `symexec` run failed before loop checking or VC generation:

```text
symexec_start=2026-04-22T22:51:41+08:00
fatal error: Expected C expression in .../annotated/verify_20260422_224852_string_collapse_spaces.c:23:1
Now parsing : n with type :2
```

The failure is at the closing brace after the function contract, before the body is symbolically executed. I checked successful examples and found `n@pre` is used for real C parameters, for example `array_remove_value_to_output(int n, ...)`, but this task's `n` is only a ghost variable from `With l d n`; there is no C variable named `n`. Therefore the front end tries to parse `n@pre` as a pre-state C expression and fails before it can verify any annotations.

The original input contract contains:

```c
Ensure
  exists t,
    Zlength(t) == n@pre - Zlength(string_collapse_spaces_spec(l)) &&
    CharArray::full(s, n@pre + 1, app(l, cons(0, nil))) *
    CharArray::full(out, n@pre + 1,
      app(app(string_collapse_spaces_spec(l), cons(0, nil)), t))
```

Because ghost `n` is immutable across the function, replacing `n@pre` by `n` in the active annotated copy is a parser normalization rather than a semantic strengthening or weakening. I will not modify `input/string_collapse_spaces.c`; the change is limited to `annotated/verify_20260422_224852_string_collapse_spaces.c` so `symexec` can parse the task. The same normalization is needed inside the loop invariant and exit assertion, because those annotations also mention ghost `n@pre`.

After normalization, the key invariant shape remains the same, except all ghost-length bounds use `n`:

```c
0 <= i && i <= n &&
0 <= j && j <= i &&
Zlength(l) == n &&
Zlength(d) == n + 1 &&
Zlength(lout) == n + 1 &&
...
CharArray::full(s, n + 1, app(l, cons(0, nil))) *
CharArray::full(out, n + 1, lout)
```

The exit assertion likewise fixes `i == n` and `j == Zlength(string_collapse_spaces_spec(l))` before `out[j] = 0`.

## 2026-04-22 annotation round 3

After normalizing ghost `n@pre`, `symexec` reached the body but rejected the invariant:

```text
fatal error: Use of undeclared identifier `sublist' in .../annotated/verify_20260422_224852_string_collapse_spaces.c:50:4
Symbolic Execution into function string_collapse_spaces
symexec_status=1
```

The failed invariant used `string_collapse_spaces_spec(sublist(0, i, l))` directly:

```c
j == Zlength(string_collapse_spaces_spec(sublist(0, i, l))) &&
lout[p] == string_collapse_spaces_spec(sublist(0, i, l))[p]
```

Although several integer-array examples use `sublist`, the nearby string examples avoid it and instead carry an explicit split of the input list:

```c
/*@ Inv exists l1 l2,
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      ...
*/
```

I will rewrite this task's invariant to the same prefix/suffix shape. The new invariant carries `lin` as the processed input prefix, `lrest` as the unprocessed suffix, and `dout` as the current output suffix:

```c
/*@ Inv exists lin lrest dout,
      0 <= i && i <= n &&
      0 <= j && j <= i &&
      (in_space == 0 || in_space == 1) &&
      s == s@pre &&
      out == out@pre &&
      l == app(lin, lrest) &&
      Zlength(lin) == i &&
      Zlength(l) == n &&
      Zlength(d) == n + 1 &&
      Zlength(dout) == n + 1 - j &&
      j == Zlength(string_collapse_spaces_spec(lin)) &&
      (in_space == 0 => (i == 0 || l[i - 1] != 32)) &&
      (in_space == 1 => (0 < i && l[i - 1] == 32)) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil))) *
      CharArray::full(out, n + 1, app(string_collapse_spaces_spec(lin), dout))
*/
```

This avoids `sublist` entirely in the annotation and makes the output heap shape closer to the final postcondition. Initialization uses `lin = nil`, `lrest = l`, and `dout = d`. A write case extends `string_collapse_spaces_spec(lin)` by one output character and consumes the head of `dout`; a suppressed repeated-space case extends `lin` but leaves `j` and the output heap shape semantically unchanged because the collapsed prefix does not grow. The loop-exit assertion is similarly rewritten to `exists dout` with `CharArray::full(out, n + 1, app(string_collapse_spaces_spec(l), dout))`, which is the direct pre-state for the final `out[j] = 0` write.

## 2026-04-22 annotation round 4

The prefix/suffix rewrite removed `sublist`, but `symexec` failed while aligning loop invariant pre-assertions:

```text
fatal error: The number of now assertions and loop inv pre assertions does not match.
in .../annotated/verify_20260422_224852_string_collapse_spaces.c:46:4
```

The invariant still had disjunctions:

```c
(in_space == 0 || in_space == 1) &&
(in_space == 0 => (i == 0 || l[i - 1] != 32)) &&
```

This matches the documented assertion pitfall: multi-case facts in one assertion can make the front end split cases inconsistently. I will replace them with a numeric range fact and a single guarded implication:

```c
0 <= in_space && in_space <= 1 &&
(in_space == 0 && 0 < i => l[i - 1] != 32) &&
(in_space == 1 => (0 < i && l[i - 1] == 32)) &&
```

This preserves the intended state information. `in_space` is still known to be either 0 or 1 because it is an integer in the range `[0,1]`; when it is 0 and there is a previous character, that previous character is not a space; when it is 1, there is a previous character and it is a space. The initialization remains valid (`in_space = 0`, `i = 0` makes the guarded implication vacuous), and the branch updates still establish the right case after `i++`.

## 2026-04-22 annotation round 5

After flattening the disjunctions, `symexec` progressed past invariant parsing but failed at the post-loop exit assertion:

```text
fatal error: Error: Fail to Remove Memory Permission of in_space:90
in .../annotated/verify_20260422_224852_string_collapse_spaces.c:77:1
Address found : null
```

The failing annotation is the `Assert exists dout, ...` placed after the loop and before `out[j] = 0`. This is the exact failure mode described in `ASSERTION.md`: a loop-exit assertion placed after the loop can interfere with local permission cleanup, especially for local variables that are not mentioned in the assertion (`in_space` here).

I will remove the explicit post-loop assertion. The remaining invariant still preserves the necessary state and heap resources:

```c
exists lin lrest dout,
  l == app(lin, lrest) &&
  Zlength(lin) == i &&
  j == Zlength(string_collapse_spaces_spec(lin)) &&
  CharArray::full(out, n + 1, app(string_collapse_spaces_spec(lin), dout))
```

When the loop exits, the guard branch has observed `s[i] == 0`; together with the invariant and no-zero precondition for `l[0..n)`, the generated return witness should be able to prove `i == n` and therefore `lin == l`. If this becomes a pure list/arithmetic witness in Coq, it belongs to proof rather than another assertion that breaks local cleanup.

## 2026-04-22 annotation round 6

Manual proof of the initial invariant exposed an avoidable invariant burden. The current invariant includes:

```c
Zlength(d) == n + 1 &&
Zlength(dout) == n + 1 - j &&
```

The first manual proof then requires `Zlength d = n + 1`, which is implied by `CharArray::full(out, n + 1, d)` but is not a pure contract fact. Coq's `prop_apply CharArray.full_length` focused repeatedly on the input `CharArray.full(s, ...)`, leaving the output length fact awkward to extract. More importantly, these pure suffix-length facts are not needed by the symbolic executor: the heap predicate already carries the output buffer length, and the final proof can derive suffix length from `CharArray.full out (n + 1) (string_collapse_spaces_spec lin ++ dout)` when needed.

I will simplify the invariant by removing both `Zlength(d) == n + 1` and `Zlength(dout) == n + 1 - j`. This does not weaken the memory shape; it only avoids duplicating length information already present in `CharArray::full`. Because this changes VC shape, I must rerun `symexec` and discard the previous generated proof edits.
