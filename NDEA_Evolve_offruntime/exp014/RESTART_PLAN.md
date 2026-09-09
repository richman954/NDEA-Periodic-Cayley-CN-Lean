# Restart recap and proposed continuation — September 8, 2026, evening EDT

Recorded UTC: 2026-09-09T00:28:17.361705+00:00

This is a recovery audit and plan, not a new proof result. No Lean proofs were
rerun and no Colab VM was allocated during the audit. All sealed sources and
packets were preserved.

## Completed work

- Exp011: reconstructed numerical fields converge uniformly to the concrete
  classical periodic Schrödinger solution. Local and independent checks: 44 audits.
- Exp012: uniqueness among classical periodic solutions for that concrete model;
  this connects the existing construction and numerical convergence to the unique
  PDE solution. Local and independent checks: 46 audits.
- Exp013: reusable energy/forcing balance, conservation and uniqueness for
  complex Hilbert-valued periodic systems with Hermitian variable potentials.
  Local and independent checks: 64 audits. General variable-potential existence
  was not part of the completed result.

Fresh receipt, packet SHA-256, size, ZIP CRC, manifest and payload checks passed
for all three. Their sealed on-disk payloads and accepted transferred evidence
also match. Exp013 packet was sealed at 15:01:50 UTC (11:01:50 a.m. EDT).

## Exact stopping point

Exp014 is unfinished. Its target is global classical existence and uniqueness
for i u_t = -u_xx + V(x)u on period 2*pi, with arbitrary complex Hilbert fiber,
regular Fourier initial coefficients and selfadjoint potential coefficients
having finite second weighted absolute Fourier moments.

Four modular checks passed, with current source, log and compiled artifact
hashes reverified:

- `StrongOperatorDerivative`: `evidence/20260908T152638.351560Z_StrongOperatorDerivative.json`
- `GlobalLinearEvolution`: `evidence/20260908T153640.533133Z_GlobalLinearEvolution.json`
- `WeightedFourier`: `evidence/20260908T154255.757075Z_WeightedFourier.json`
- `ScalarSeries`: `evidence/20260908T154600.238352Z_ScalarSeries.json`

The FourierPotential retry began at 15:53:38 UTC (11:53:38 a.m. EDT).
`evidence/20260908T155338.932620Z_FourierPotential.json` has no exit code or
completion hashes and its log is empty. It is interrupted evidence, not a pass.
The current source matches that launch receipt. The later FourierSynthesis,
FourierProduct, ClassicalExistence and Controls drafts are present without
completed check receipts.

The last pre-restart checkpoint is
`/home/richman954/NDEA_Recovery/snapshots/exp014_recovery_20260908T155543.797372Z_9546dbd1.zip`.
Its SHA-256 is `6a6e00f88b18753f8da1a82b718ce1552b52cbc6d725c4a588586564ed9fc690`.
All 100 captured payloads and its dated receipt hash passed verification; all
11 saved Lean files match the current workspace. Published at 15:55:43 UTC
(11:55:43 a.m. EDT). A new checkpoint will preserve this audit and plan.

## Local and Colab readiness

The pinned local Lean 4.31.0 binary and Mathlib commit were reverified, and the
local development artifacts remain present. The old watcher did not survive;
its saved running status and session/PID are historical.

The installed Colab CLI successfully queried the account during this audit:
`Pruned 4 stale local session(s). No active sessions found on server.`
A fresh runtime will be needed. The previous Exp014 allocation failed with
TooManyAssignmentsError (HTTP412) at 15:50:34 UTC, before shutdown. This is
historical; current allocation availability has not been tested.

Saved bootstrap, upload preparation and evidence-validation scripts exist in
`remote_check/`. Exp014 REPRODUCE.md and SAVED_FILES.md describe intended final
artifacts; they do not establish that those artifacts exist. In particular,
there is no allocated Exp014 VM receipt, prepared bootstrap archive, combined
source/final inputs, final combined result, or sealed Exp014 packet yet.
`start_bootstrap.py` is still UNPREPARED. Prepare and pin the actual inputs
before uploading or launching it.

## Proposed sequence when work resumes

1. Take a checkpoint and start a tracked minute watcher. Confirm an immediate
   save and another advancing checkpoint after an interval.
2. Resume FourierPotential using a new timestamped receipt. From exp014:
   `python3 -B run_lean.py lean/FourierPotential.lean`.
   Preserve the previous failed and interrupted logs.
3. Complete and check FourierSynthesis, FourierProduct, ClassicalExistence and
   Controls in dependency order. Establish the actual PDE and initial condition,
   then apply Exp013 uniqueness under the precise checked hypotheses.
4. Review and freeze exact sources; prepare the combined proof and pinned
   delivery artifacts. Run isolated local verification and an independent
   fresh Colab CPU check. The allocation command, when needed, is
   `/home/richman954/.local/bin/colab new --session exp014-independent-check`.
   Record the real allocation and empty initial environment, then bootstrap
   independent pinned dependencies. A new allocation is still required.
5. Download and verify independent evidence, seal Exp014 after both accepted
   checks, and make a verified Chromebook backup covering completed packets
   001–014. Take a final checkpoint after all notes and receipts are updated.

After this milestone, a proposed next direction is extending numerical
convergence to the enlarged variable-potential class, using quantitative
forcing/residual stability as a bridge. That is a later scope decision.

The verified existing Downloads backup is
`/home/richman954/Downloads/NDEA_Backup_2026-09-08_150319Z_9a2eb2`.
It covers completed work through Exp013; active Exp014 is preserved separately
in local recovery checkpoints. Open Files → Linux files → Downloads.
Google Drive backup remains canceled; local Chromebook storage is the chosen
backup destination.
