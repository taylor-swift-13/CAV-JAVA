---
name: c-qcp-eval
description: Evaluate an existing C/QCP implementation against concrete positive and negative cases by treating the attached contract as the semantic target.
---

Use this workflow independently from contract, verify, and audit. The goal is
to decide whether the contract attached to an implementation correctly
characterizes that implementation's behavior on representative concrete inputs.
Do not modify the implementation, its contract, or any `.v` helper file.

## Required References

- `experiences/general/EVAL.md`
- `experiences/general/AUDIT.md`
- `experiences/general/CONTRACT.md`

## Inputs

- Implementation/spec C file.
- Optional companion `.v` file.
- Target function.
- Workspace path.
- Cases directory and evaluation directory.

## Output Layout

```text
output/eval_<timestamp>_<name>/
  original/<name>.c
  original/<name>.v            # optional copy when provided
  cases/cases.json
  evaluation/evaluation.json
  logs/test_reasoning.md
  logs/issues.md
  logs/metrics.md
  logs/final_result.md
  logs/agent_prompt_<run>.txt
  logs/agent_stdout_<run>.{jsonl,log}
  logs/agent_stderr_<run>.log
  logs/agent_last_message_<run>.txt
```

## Cases

Generate exactly the requested number of positive and negative cases in
`cases/cases.json`.

- Positive cases satisfy every `Require` clause.
- Negative cases either violate a precondition or claim a return value / post
  state that should be rejected by `Ensure`.
- Prefer adversarial coverage: hit every branch and every postcondition shape.

Schema:

```json
{
  "function_name": "abs_value",
  "positive": [
    {
      "id": "pos01",
      "description": "negative branch",
      "inputs": {"x": -3},
      "result": 3,
      "post_state": {}
    }
  ],
  "negative": [
    {
      "id": "neg01_wrong_output",
      "kind": "postcondition",
      "description": "claims a wrong return value",
      "inputs": {"x": -3},
      "result": -3,
      "post_state": {},
      "violated_clause": "__return >= 0"
    }
  ]
}
```

## Evaluation

For each case, evaluate the contract clauses against the concrete values.
Mechanical substitution is preferred; if a clause depends on external Coq
predicates or other semantics that cannot be decided mechanically from the case,
reason about it explicitly and record why.

Write `evaluation/evaluation.json`:

```json
{
  "cases": [
    {
      "id": "pos01",
      "verdict": "pass",
      "clauses": [
        {
          "clause": "__return >= 0",
          "substituted": "3 >= 0",
          "evaluated": true
        }
      ]
    }
  ]
}
```

Allowed case verdicts:
- `pass`
- `fail`
- `needs_judge`

If `needs_judge` is used, include a `judge` object with `verdict` and `reason`.

## Aggregate Verdict

Write `logs/final_result.md` with one of:

- `Spec verdict: Correct`
- `Spec verdict: Buggy`
- `Spec verdict: Inconclusive`

Rules:
- `Correct`: every positive passes, every negative fails, and nothing remains
  undecided.
- `Buggy`: at least one positive fails, or at least one negative passes.
- `Inconclusive`: some clause or case could not be resolved decisively.

## Anti-Cheating Rules

- Do not rewrite the contract to fit the cases.
- Do not treat unreachable-code tricks as valid negative cases.
- Do not claim `Correct` when you are actually unsure.
- Do not record experience here; only write the stage logs.

## Final Result

`logs/metrics.md` must end with exactly one of:

```text
Final Result: Success
Final Result: Fail
```

`Success` is allowed only when:
- the requested number of positive and negative cases were produced;
- `evaluation/evaluation.json` exists and covers every case;
- `logs/final_result.md` contains `Spec verdict: Correct` or `Spec verdict: Buggy`.

`Spec verdict: Inconclusive` is `Final Result: Fail`.
