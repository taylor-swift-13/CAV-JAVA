---
name: java-openjml-simple-verify
description: Run guarded OpenJML verification and record concrete failures.
---

Use this when no Codex repair loop is needed.

1. Run `scripts/check_jml_cheating.py` on the Java file.
2. Run `scripts/run_openjml_verify.sh` on the Java file.
3. Record stdout, stderr, exit code, and result in the workspace logs.
