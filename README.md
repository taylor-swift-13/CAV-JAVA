# CAV-JAVA

This repository is configured to use [OpenJML](https://www.openjml.org/) for Java/JML checking.

## Install OpenJML

Install the latest OpenJML release into the local, git-ignored `.tools/openjml` directory:

```bash
./scripts/install-openjml.sh
```

Load the environment in the current shell:

```bash
source ./scripts/env-openjml.sh
```

Verify the installation:

```bash
./scripts/check-openjml.sh
```

## Download Official Examples and Docs

Download/copy OpenJML official resources into `doc/` and `examples/`:

```bash
./scripts/sync-openjml-official-resources.sh
```

The `doc/` directory contains the OpenJML User Guide, the JML Reference Manual,
mirrored documentation/tutorial pages, and release-bundled specs. The `examples/`
directory contains local examples plus official demos, tutorial source examples,
User Guide examples, and mirrored web examples.

## Common Commands

Run ESC checking on a Java file:

```bash
openjml -esc examples/Counter.java
```

Run the guarded OpenJML wrapper used by the end-to-end workflow:

```bash
./scripts/run_openjml_verify.sh examples/Counter.java
```

Prepare a contract workspace without invoking Codex:

```bash
python3 scripts/run_codex_contract.py raw/smoke_add.md --function-name add --dry-run
```

Prepare a verify workspace without invoking Codex:

```bash
python3 scripts/run_codex_verify.py input/smoke_add.java --class-name SmokeAdd --dry-run
```

Compile with runtime assertion checking:

```bash
openjml -rac examples/Counter.java
openjml-java -cp examples Counter
```

The installer pins the downloaded release under `.tools/openjml/<version>` and updates `.tools/openjml/current` to point at it.

## End-to-End Experience Workflow

The Java/OpenJML reusable workflow notes live under `experiences/general/`.
Completed end-to-end example snapshots live under `experiences/end-end/<name>/`.
It mirrors the CAV two-stage idea without copying the C examples:

1. `contract`: raw task text to `input/<name>.java`.
2. optional `eval`: `input/<name>.java` to
   `output/eval_<timestamp>_<name>/`, with generated positive and negative
   harness cases.
3. `verify`: `input/<name>.java` to
   `output/verify_<timestamp>_<name>/verified/<name>.java`, checked by
   anti-cheating scans and `openjml -esc`.

The key rule is that `Final Result: Success` is only valid when OpenJML passes
and `scripts/check_jml_cheating.py` accepts the verified file.

There is also an independent eval skill at `skills/eval/SKILL.md` for
generating 10 positive and 10 negative OpenJML harness cases for an existing
implementation/spec.

Batch flow. It follows the CAV many-script style: pass task names, and each
name runs `contract -> verify` by default. With `--eval`, the order is
`contract -> eval -> verify`. The batch script does not create a batch
workspace; only the single-stage workspaces are kept under `output/`.
Successful verify runs are exported to `experiences/end-end/<name>/` by
default; use `--no-export-examples` to disable that. Existing same-name
examples are skipped rather than overwritten.

```bash
./scripts/run_codex_verify_many.sh --eval --timeout-seconds 3600 --jobs 1 add_two array_sum
```
