# Reproduce Experiment 008

The production/control modules are `FrequencyBounds`, `ContinuumModes`,
`FourierGrid`, `Orthogonality`, `SuperpositionClosure`, `StageBridge`, and
`Controls`. Their frozen predecessor is `lean/Exp007Foundation.lean`, copied
byte-for-byte from the verified Experiment 007 combined source. Exploratory
`OrthogonalityProbe.lean` is excluded from production module ordering.

## Environment and trust boundary

- Lean 4.31.0; compiler SHA-256
  `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- All nine dependency revisions are in
  `remote_check/bootstrap_inputs/lake-manifest.json`; the verifier pins the
  lockfile hash and checks each source checkout's revision and cleanliness.

The independent runtime is `exp008-independent-check`, root
`/content/exp008_check`. It independently downloaded the official compiler
distribution and compatible library cache. No locally compiled project
artifacts were uploaded. The bootstrap source, commands, download hashes, and
cache requests are preserved in the independent evidence.

The compiler, core libraries, and compatible compiled external libraries remain
trusted inputs. The verifier checks the compiler binary hash and records/checks
the imported library artifacts before and after execution. It does not rebuild
Lean/Mathlib, establish full source-to-artifact correspondence, or pre-pin every
core-library file. Agreement of external artifact hashes between environments
is a separate recorded check.

## Combined proof check

Reconstruct the combined source and complete public theorem/lemma audit catalog:

```bash
python3 -B make_combined.py
```

With existing installations of the pinned dependencies, choose a fresh output
directory and run:

```bash
python3 -B verify_combined.py \
  --root /absolute/path/to/exp008 \
  --lean /absolute/path/to/lean-4.31.0/bin/lean \
  --mathlib /absolute/path/to/packages/mathlib \
  --other-packages /absolute/path/to/packages \
  --output /absolute/path/to/new-verification-output
```

For the independent Colab layout, the compiler is
`/content/exp008_check/lean-4.31.0-linux/bin/lean`, Mathlib is
`/content/exp008_check/mathlib`, and the other packages are in
`/content/exp008_check/mathlib/.lake/packages`.

The verifier reconstructs exact combined bytes and the full new public audit
catalog, checks source/runner pins and proof policy, copies only imported
external library artifacts into a new isolated directory, and runs Lean with
one worker. The final combined source imports no project artifact. The complete
frozen foundation and every new production/control proof are re-elaborated.
All selected audit dependencies must be among `propext`, `Classical.choice`,
and `Quot.sound`. A successful `RESULT.json` is required; process exit alone
does not establish the full qualification.

## Supporting checks

```bash
python3 -B numerical_checks.py
python3 -B check_predecessors.py
```

Numerical diagnostics use Python's standard library and check an active finite
spectrum, actual wrapped residuals, global errors, Parseval, aliasing, and
refinement. They are floating-point diagnostics, separate from Lean proofs.
The preservation checker requires the neighboring frozen Experiment 005–007
workspace folders; the standalone packet includes their combined mathematical
foundation but does not duplicate every earlier release archive.

`remote_check/check_export.py` validates the downloaded independent evidence
against its export receipt and the current local sources/audit catalog. It
requires a new `downloaded_evidence` destination. Its successful receipt records
transfer agreement; it does not rerun the compiler.
