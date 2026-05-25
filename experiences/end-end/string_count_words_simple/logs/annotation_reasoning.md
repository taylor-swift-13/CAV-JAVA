# Annotation Reasoning

## Initial loop invariant for `string_count_words_simple`

The unannotated loop is:

```c
while (1) {
    if (s[i] == 0) {
        break;
    }
    if (s[i] == 32) {
        in_word = 0;
    } else {
        if (!in_word) {
            count++;
            in_word = 1;
        }
    }
    i++;
}
```

At the loop head, `i` is the next character index to inspect. The C state already summarized the prefix `sublist(0, i, l)` into two variables: `count` is the number of word starts seen so far, and `in_word` records whether the previous processed character leaves the scan inside a word. The most direct invariant is therefore a suffix accumulator equation:

```c
count + string_count_words_simple_go(flag, sublist(i, n, l)) ==
  string_count_words_simple_spec(l)
```

where `flag` is `false` when `in_word == 0` and `true` when `in_word == 1`. This matches the Coq definition:

```coq
Fixpoint string_count_words_simple_go (in_word : bool) (l : list Z) : Z := ...
Definition string_count_words_simple_spec (l : list Z) :=
  string_count_words_simple_go false l.
```

Initialization is immediate: before the loop, `i == 0`, `count == 0`, and `in_word == 0`, so the equation reduces to `0 + string_count_words_simple_go false (sublist(0, n, l)) == string_count_words_simple_spec(l)`. The contract gives `Zlength(l) == n`, so `sublist(0, n, l)` is the whole input list.

Preservation follows by case analysis on the current character. If `s[i] == 32`, the C code sets `in_word = 0` and does not increment `count`; the Coq helper also recurses with `false` on the tail. If `s[i] != 32` and `in_word == 0`, the C code increments `count` and sets `in_word = 1`; the Coq helper contributes `1 + go true tail`. If `s[i] != 32` and `in_word == 1`, the C code keeps `count` and leaves the scan inside a word; the Coq helper recurses with `true` on the tail.

The invariant must also preserve the unchanged input resource and enough arithmetic for memory reads and `count++`:

```c
0 <= i && i <= n
0 <= count && count <= i
0 <= in_word && in_word <= 1
s == s@pre
Zlength(l) == n
(forall (k: Z), (0 <= k && k < n) => l[k] != 0)
CharArray::full(s, n + 1, app(l, cons(0, nil)))
```

On loop exit, the program has just read `s[i] == 0`. Together with the contract fact that every `l[k]` for `0 <= k < n` is nonzero and the heap shape `app(l, cons(0, nil))`, this should force `i == n`. A small loop-exit `Assert` immediately after the loop records `i == n` and `count == string_count_words_simple_spec(l)` before the local variables are cleaned up at `return count;`.

## Revision after bool-literal frontend failure

The first `symexec` attempt failed before VC generation:

```text
fatal error: Use of undeclared identifier `false' in .../annotated/verify_20260423_014132_string_count_words_simple.c:40:4
```

The failed invariant used direct Coq bool literals:

```c
count + string_count_words_simple_go(false, sublist(i, n, l)) == ...
count + string_count_words_simple_go(true, sublist(i, n, l)) == ...
```

This is a frontend parsing issue, not a semantic problem with the loop. To avoid bool literals in C annotations, the next revision removes the direct `string_count_words_simple_go` use and switches to a prefix-summary invariant over the exported `string_count_words_simple_spec`:

```c
count == string_count_words_simple_spec(sublist(0, i, l))
```

The C variable `in_word` is then related to the last processed character using only integer facts:

```c
(i == 0 => in_word == 0)
(0 < i && in_word == 0 => l[i - 1] == 32)
(in_word == 1 => 0 < i && l[i - 1] != 32)
```

This still supports preservation. When the current character is a space, `in_word` becomes `0`, and the prefix word count does not increase. When the current character is non-space and `in_word == 0`, the previous prefix is empty or ended in a space, so appending this character starts one new word and `count++` matches the spec. When `in_word == 1`, the previous prefix ended in a non-space character, so appending another non-space character does not start a new word and `count` is unchanged. The exit assertion remains the same shape as the nearby string counting examples: it fixes `i == n`, `count == string_count_words_simple_spec(l)`, and the preserved `CharArray::full` resource immediately before `return count;`.

## Revision after `sublist` frontend declaration failure

After replacing the bool-helper invariant with a prefix invariant, `symexec` failed before VC generation with:

```text
fatal error: Use of undeclared identifier `sublist' in .../annotated/verify_20260423_014132_string_count_words_simple.c:37:4
```

The failing annotation line was:

```c
count == string_count_words_simple_spec(sublist(0, i, l))
```

This workspace imports `verification_list.h`, but the annotation frontend still requires a direct `Extern Coq` declaration for some polymorphic symbols used in string annotations. The existing `string_copy_prefix` verified workspace used this exact declaration to resolve the same frontend error:

```c
/*@ Extern Coq (sublist : {A} -> Z -> Z -> list A -> list A) */
```

The next edit adds that declaration near the existing `Extern Coq` line. The invariant itself is unchanged; this is only a frontend symbol-table fix so the same prefix-summary VC can be generated.

## Revision after post-loop local permission failure

With `sublist` declared, `symexec` reached the loop-exit assertion but failed with:

```text
fatal error: Error: Fail to Remove Memory Permission of in_word:84 in .../annotated/verify_20260423_014132_string_count_words_simple.c:62:4
```

The post-loop assertion was:

```c
/*@ Assert
      i == n &&
      0 <= count && count <= n &&
      s == s@pre &&
      Zlength(l) == n &&
      count == string_count_words_simple_spec(l) &&
      ...
*/
```

At this program point, `in_word` is still a live local variable, but the assertion forgot to mention it. The frontend therefore tried to remove its local-store permission while checking the assertion. The next edit keeps the assertion semantically identical for the postcondition but adds the pure bound already present in the loop invariant:

```c
0 <= in_word && in_word <= 1
```

This does not strengthen the algorithmic claim; it only keeps the live scalar local represented through the assertion boundary so symbolic execution can proceed to `return count;` and then clean up locals in the normal order.
