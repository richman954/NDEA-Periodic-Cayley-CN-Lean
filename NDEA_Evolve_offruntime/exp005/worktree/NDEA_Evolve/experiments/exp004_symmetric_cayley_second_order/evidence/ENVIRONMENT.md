# Experiment 004 verification environment

The predecessor `lean-toolchain`, `lake-manifest.json`, and project
configuration are preserved byte for byte. The Mathlib checkout was checked
at commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
Its tracked worktree and index were also checked clean; the final assurance
audit repeats these checks and compares each selected receipt to the pinned
Lean executable identity below.

The explicit Lean 4.31.0 executable is
`/home/richman954/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean`.
Its SHA-256 is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The runner records this binary hash, full command, environment search path,
source/output hashes, timestamps, timeout, exit status, and log hash for each
invocation. Each Lean command uses `-j 1` and `LEAN_NUM_THREADS=1`.
The shared exclusive lock is `/tmp/exp003_lean_one_job.lock`; a competing
runner is rejected instead of launching another job. Default timeout is
900 seconds per command.

Compatible cached import artifacts are copied from the existing packages at
`/home/richman954/NDEA/workspace/NDEAMathlibGate/.lake/packages` into the
separate disposable `/tmp/exp004_build/lib/lean` cache. The first preparation
copied an import closure of 9,468 artifacts totaling 1,746,661,568 bytes;
later preparations for additional control imports have distinct receipts.
This is an ordinary temporary-filesystem build, not a tmpfs claim.

The first two predecessors use the inherited Step 2 import-only shadows.
All later predecessors and new modules use their production sources.
Non-import source equality is checked for the shadows. No package download,
dependency update, root-project Lake build, remote execution, numerical
sampling, or remote publication is needed for this campaign.

Development attempts remain attributable even when they fail. Only fresh
successful final modular and combined runs, with hashes matching the final
delivered source, qualify the release. The combined source contains the full
eight-module predecessor chain and new production/control proof bodies, and
does not import project `.olean` artifacts.
