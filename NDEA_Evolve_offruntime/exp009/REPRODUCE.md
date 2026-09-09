# Reproduce Experiment 009

The final packet contains the complete frozen predecessor source and every new
module. Work in a copy when reproducing checks so that accepted receipts remain
preserved. `evidence/FINAL_VERIFICATION.json` and `PACKET_MANIFEST.json` describe
the accepted files; development logs with nonzero exits are historical attempts.

## Required compiler and libraries

Use Lean 4.31.0. The expected `bin/lean` SHA-256 is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Use the exact clean source revisions in
`remote_check/bootstrap_inputs/lake-manifest.json`, including Mathlib
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Compatible compiled external library
artifacts must be present in each package's `.lake/build/lib/lean` directory.

The Experiment 009 independent environment is a newly allocated replacement
Colab CPU VM, session `exp009-independent-check`, documented in
`remote_check/ENVIRONMENT_EXPECTED.json`. Its compiler and external libraries
are independently downloaded under `/content/exp009_check`; the bootstrap
driver and exact input bundle are retained in `remote_check/bootstrap.py` and
`remote_check/bootstrap_inputs/`. The earlier `exp008-fresh-recheck-r2` runtime
became unavailable before the Experiment 009 independent proof check. Its
prepared request, environment record, and scripts remain in
`remote_check/lost_runtime/`; the accepted local proof and prior sealed packets
were unaffected.

The combined verifier also works with another installation of the pinned
compiler and libraries. It checks revisions, tracked source cleanliness, and
the compiler binary, then records the artifact hashes. Downloaded compiler and
library artifacts remain trusted inputs.

## Combined proof check

From the restored experiment directory, regenerate the combined source:

```sh
python3 -B make_combined.py
```

Then supply paths to your pinned compiler, Mathlib checkout, and the directory
containing the other pinned package checkouts. The output directory must be new:

```sh
python3 -B verify_combined.py \
  --root . \
  --lean /path/to/lean-4.31.0-linux/bin/lean \
  --mathlib /path/to/mathlib \
  --other-packages /path/to/mathlib/.lake/packages \
  --output /path/to/new-verification-directory
```

The verifier reconstructs the exact combined bytes and complete new public
axiom catalog. It checks proof policy, copies only the external import closure,
re-elaborates all project source with project artifacts excluded, validates
every axiom print, and checks source/library hashes before and after. The final
`RESULT.json` must contain `passed: true`; an empty log or a process exit alone
does not satisfy acceptance.

The development helper `run_lean.py` uses paths from the original workstation
and predecessor modular artifacts. It is convenient in that workspace; the
combined verifier above provides the portable source check.

## Diagnostics and evidence

`python3 -B numerical_checks.py` reruns the supporting floating-point diagnostics
using the Python standard library. Its separate analytic bound covers the
omitted reference modes, not floating-point roundoff. Run it in a copy because
it writes `evidence/numerical_checks.json`.

`remote_check/check_download.py` validates a downloaded evidence archive against
an accepted local combined run and the exact uploaded inputs. It requires the
archive SHA-256 and a fresh extraction directory. The accepted archive checksum
is in `remote_check/EXPORT_RECEIPT.json`; this transfer checker does not rerun Lean.

`check_predecessors.py` additionally checks the older experiment manifests in
the original workspace. `finalize.py` qualifies all modular/combined/numerical
receipts and creates the final packet after reports and evidence are complete.
It refuses to replace an existing packet.
