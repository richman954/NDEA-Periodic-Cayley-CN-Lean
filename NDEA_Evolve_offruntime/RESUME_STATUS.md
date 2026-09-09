# Recovery status — September 9, 2026 UTC

Latest milestone: Experiment014 is complete and sealed; Exp015 is the active extension.
Read exp015/PLAN.md and current task state for ongoing forcing/residual stability work.
For restart recovery, first read `/home/richman954/NDEA_Recovery/START_HERE.md`
and `TASK_STATE.json`. Older sections are historical records.

The Chromebook restart did not remove the frozen Experiment 005 release at
`exp005/releases/20260907_verified_final/`. Archive and bundle checksums were
rechecked successfully after restart. The preserved release commit is
`1cb91755d0c8a6c681334907785de58b0bf53d6c`.

## Independent verification completed

Replacement Colab session: `exp005-independent-check-r2`.
Remote root: `/content/exp005_independent_check`.
Current runner: `exp005/independent_checks/colab_20260908/verify_remote_r3.py`.
Launch time: `2026-09-08T04:45:13.309425+00:00`, PID 5744.
Runner SHA-256: `042ed6bc69904d3fab01ab13e42ea09c6ecd814c25d90b7eb9368295cc563b2a`.

The remote run completed successfully at `2026-09-08T04:52:58.812987+00:00`.
All fourteen modular Lean invocations, the combined proof check, and forty
theorem audits passed. No previous project build artifacts were used. The
pinned compiler and compatible library cache were downloaded independently;
Lean and Mathlib themselves were not rebuilt from scratch.

Final evidence is downloaded and extracted under
`exp005/independent_checks/colab_20260908/final_evidence_20260908T045723Z/`.
The full proof result is `evidence/20260908T044513/portable_verification/RESULT.json`
inside that directory. The adjacent `FINAL_TRANSFER_CHECK.json` confirms the
archive hash, all 220 evidence-file hashes, 67 completed command-log hashes,
and agreement between the combined compiler audit and the report.

Archive: `exp005_remote_evidence_20260908T045723Z.tar.gz`.
SHA-256: `8aa1ed6b9b9013f5c02738dd7123b94a080bb009d56dc8150cc5a47e50f37b50`.

Runner r2 failed before any external commands because its custom archive
extractor rejected the top-level directory. Runner r3 delegates restoration to
the tested portable verifier. Keep failed evidence alongside the final run.

## Experiment 006 completed

Experiment 006 is isolated in `exp006/`. All new modular files now pass Lean:
the real periodic grid, scalar PDE/residual estimates, actual Exp005 matrix
factor bridge, concrete fixed-time error, varying-mesh convergence, and six
exact controls. Local and independent Colab combined checks both passed all
41 audits (35 production theorems and six controls), with only the three
standard Lean axioms. The local check took 161.608 seconds; the independent
check took 141.621 seconds and finished at `2026-09-08T05:21:05.754663+00:00`.

The concrete solution is `U(t,x)=exp(i(x-2t))`, solving `i U_t=-2 U_xx` on
period `2*pi`, with both split generators equal to the centered negative
second difference. Under `0<h<=1`, `0<=k<=2`, and `n*h=2*pi`, the proved
stage budget uses `Ct=(5/16)*sqrt(2*pi)` and `Cs=(1/4)*sqrt(2*pi)`.
This is a single nonzero Fourier mode with commuting operators.

Combined source: `exp006/lean/CombinedVerification.lean`.
SHA-256: `af3d14716b492f6485dd1bcf88c3c99cd13440a219f89b27b5258531d7f96c52`.
Expected audit names: `exp006/evidence/EXPECTED_FINAL_THEOREMS.json` (41).
Remote root: `/content/exp006_check` on `exp005-independent-check-r2`.
The independent evidence is downloaded into `exp006/remote_check/final_evidence/`.
Its transfer audit confirms all 22 evidence-file hashes and agreement of the
41 theorem audits with the locally checked source. Read
`exp006/COMPLETION_REPORT.md` for the final outcome, scope, and evidence links.
No proof checks remain running. General smooth/noncommuting split PDEs remain
a future extension, beyond the completed concrete-mode result.

The frozen Experiment 005 files have not been edited. Its independent review
packet is `/home/richman954/Exp005_Independent_Verification_Packet_20260908.zip`
with a neighboring checksum file.

Final Experiment 006 review packet:
`/home/richman954/Exp006_Verified_Review_Packet_20260908.zip`.
SHA-256: `1cac6774bdff6d605b711d8a43ea497134937ffefef15371449f428d539b4284`.
Its 99 packaged proof/evidence file hashes were checked, and the earlier
21-entry local verified manifest remains unchanged. Both requested work
streams are complete and preserved locally.

## Experiment 007 completed

The concrete noncommuting periodic spinor closure is complete and sealed in
`exp007/`. Its model is `i U_t = -U_xx + (Z+X)U`, with Pauli diagonal/swap
matrices and reference `U(t,x)=exp(ix)exp(-it(I+Z+X))v0`. Actual real PDE
derivatives, wrapped grid stencils, unique CN stages, full-grid noncommutation,
unitarity, Fourier lifting, concrete error, varying-mesh convergence, and the
exact Exp005 stage-budget bridge are proved.

For `0<h<=1`, `0<=k<=1/6`, `d*h=2*pi`, and `N*k<=T`:
`e_N <= e_0 + sqrt(2*pi)*T*(27000*k^2+h^2/8)*norm(v0)`.
The actual stage budget uses constants `29250` and `13/96`. Arbitrary numerical
initial grid states retain their full weighted initial error. The continuum
reference class remains one spatial Fourier mode with constant internal
coupling; spatial mode mixing and variable potentials are future work.

All seven new modules pass locally and on fresh Colab. Both complete combined
checks passed all 88 public theorem audits (81 production + 7 controls), using
only `propext`, `Classical.choice`, and `Quot.sound`. Local elapsed time:
289.022 seconds; independent: 162.250 seconds. All 9,868 isolated external
library artifact hashes match between the environments and remained unchanged.
The compiler/library cache were independently downloaded; Lean and Mathlib
were not rebuilt from source. No project artifacts entered the combined runs.

Combined source SHA-256:
`cdb0fd44edea6e81b761af02304deada2e7ff7c9ebea1936c4e664acc1f0456c`.
See `exp007/COMPLETION_REPORT.md`, `exp007/REPRODUCE.md`, and
`exp007/evidence/FINAL_VERIFICATION.json`.

Independent evidence is preserved under
`exp007/remote_check/downloaded_evidence/exp007_independent_evidence/`.
All 118 evidence-file hashes and 88 audits passed transfer validation.
Remote archive SHA-256:
`fe0de6ba7936fe651352c14589b5a3fa800ad1473f1d085206e47b59cb7e0308`.
Fresh runtime was `exp007-independent-check`, root `/content/exp007_check`.
No verification work remains running or required; evidence is preserved locally.

Final review packet:
`/home/richman954/Exp007_Verified_Review_Packet_20260908.zip`.
SHA-256: `cb527b6245b11cdeb044a97e60aa9201cf20bfc8c60dac99642d91677a7f7b5f`.
All 217 manifest entries plus the manifest itself were verified inside the ZIP.
`exp007/evidence/FINAL_PACKET_RECEIPT.json` records its size, hashes, and checks.
The frozen Exp005 889-entry and Exp006 21/99-entry manifests remain unchanged.

## Experiment 008 completed and sealed

The finite Fourier superposition milestone is complete in `exp008/`. The same
noncommuting periodic spinor PDE now admits arbitrary finite signed integer
frequencies and complex two-component coefficients. For a fixed cutoff `M>=1`,
`|m|<=M`, `d>2M`, `d*h=2*pi`, `h>0`, `M*h<=1`, `k>=0`,
`2*k*(M^2+2)<=1`, and `N*k<=T`, the proved weighted error is
`e_N <= e_0 + sqrt(2*pi)*T*(Ct(M)*k^2+Cs(M)*h^2)*sqrt(sum norm(a_m)^2)`,
where `Ct(M)=1000*(M^2+2)^3` and `Cs(M)=M^4/8`.
The actual stage budget is derived with the additional factor `9/8` and a
single-step factor `k`. Arbitrary numerical initialization retains its full
weighted initial error. Fixed-band mesh convergence is proved. Growing cutoffs,
infinite Fourier data, and spatially varying potentials remain outside this result.

All seven new modules pass locally and on fresh Colab. Both combined checks
passed all 90 new public audits (83 production + 7 controls), using only the
three standard axioms. Local compile: 381.085 seconds; independent: 278.878
seconds, completed `2026-09-08T08:00:58.930428+00:00`. Combined source SHA-256:
`5fbcbcb39be7d68145f1c74f7210f45f5e067cea68a43a49342cd40e040752a0`.
All 9,868 external artifact hashes agree and remained unchanged. Compiler and
library artifacts remain trusted inputs; Lean/Mathlib were not rebuilt, and
these checks do not prove source-to-artifact correspondence.

The fresh runtime was `exp008-independent-check`, root `/content/exp008_check`.
All evidence is saved locally under
`exp008/remote_check/downloaded_evidence/exp008_independent_evidence/`.
The transfer check verified 138 files and every uploaded verification input.
Independent archive SHA-256:
`d048128f208c87ee528ea2c4cbd264de2dc400414b37d04c232d513734206692`.
The frozen predecessor manifests still match all 889/21/99/217 entries.

Read `exp008/COMPLETION_REPORT.md`, `exp008/SAVED_FILES.md`, and
`exp008/evidence/FINAL_VERIFICATION.json` for the accepted result and checkpoint map.
Final packet: `/home/richman954/Exp008_Verified_Review_Packet_20260908.zip`.
SHA-256: `8e2b429c161443901be17a585562af2ce5f920b44283044ba3e5f14bd99330a7`.
All 254 payload hashes plus exact manifest bytes were verified inside the ZIP;
its receipt is `exp008/evidence/FINAL_PACKET_RECEIPT.json`.
No proof checks remain running or required for Experiment 008.

The completed recap is `recap_001_007_20260908/MASTER_RECAP.md`; its searchable
index and checkpoint/archive map cover the earlier saves. The home convenience
archive is `Experiments_001-007_Recap_and_File_Index_20260908.zip`.

## Additional fresh VM double-check completed and sealed

The user requested another new Colab VM to double-check the completed work.
New evidence is isolated in `exp008/independent_checks/colab_r2_20260908/`.
The original Exp008 packet and all 254 sealed payload hashes passed the final
preservation check. Earlier Exp005–007 manifests also remain unchanged.

Fresh CPU session: `exp008-fresh-recheck-r2`, VM
`m-s-kkb-usc1b1-2yftnii3g1zpd`, distinct from the earlier Exp008 VM.
Remote root: `/content/exp008_check`. Fresh initialization found no prior
project runtime paths. Pinned compiler/dependency bootstrap and full Mathlib
cache fetch passed. The exact sealed 90-audit combined check passed in
247.136 seconds, completed `2026-09-08T08:27:09.311646+00:00`.

The completed supplementary suite checked 332 retained public declarations plus
141 omitted historical declarations (473 distinct audits through Exp001–008),
four anonymous Exp001 positive examples, and 13 intended false-claim
rejections across six negative-control drivers. Historical proof bodies are
unchanged; only imports/audit commands are reorganized for standalone checks.

All 473 public theorem/control audits passed with only the three standard
axioms; all 13 intended false-claim rejections matched their expected proof
diagnostics. These counts include supporting lemmas and control witnesses.
The supplementary suite completed at `2026-09-08T08:43:08.262472+00:00`, with
all 34,168 isolated external artifact hashes unchanged. The exact Exp008
source, its 90 audits, and its 9,868 library hashes agree across the original
local run and both independent Colab VMs. The 90 are included in the 473 total.

The unchanged Exp008 numerical rerun passed 60 stage and 20 global-error cases,
plus refinement and aliasing checks. These are supporting floating-point
diagnostics; not every earlier numerical script or archive-restoration exercise
was rerun. Downloaded compiler and compatible library artifacts remain trusted
inputs; Lean and Mathlib were not rebuilt from source.

All 180 transferred evidence-file hashes passed receiving validation. Read
`exp008/independent_checks/colab_r2_20260908/REPORT.md` for scope and results,
`SAVED_FILES.md` in that folder for the saved checkpoints, and
`FINAL_VERIFICATION.json` for the accepted final record. The new evidence
archive SHA-256 is
`d28f0ae365647d4386e7fc5e81f9499efae882709519a8360f2ff0e1e667f16c`.

Final packet:
`/home/richman954/Experiments_001-008_Fresh_VM_Recheck_20260908.zip`.
SHA-256: `95f8fc6d27975d0a59fbea3f9e0a6517369131342d8abbdecb9923606d545a4c`.
All 340 payload hashes plus the exact manifest bytes and ZIP CRCs passed.
The packet was sealed at `2026-09-08T08:47:27.523830+00:00`; its receipt is
`exp008/independent_checks/colab_r2_20260908/FINAL_PACKET_RECEIPT.json`.
A neighboring `.zip.sha256` file records the archive checksum.
No proof checks remain running or required for this additional verification.

## Experiment 009 completed and sealed

The user authorized the next mathematical milestone after the additional VM
check. Work is isolated in `exp009/`: actual infinite Fourier references with
absolutely summable coefficient norms, sampled truncation-tail bounds, and
convergence with a growing frequency cutoff. Read `exp009/PLAN.md` for the
precise acceptance criteria and the distinction between this Fourier evolution
reference and a classical PDE statement requiring additional derivatives.
The full-grid error must retain both initial and terminal truncation tails.

The proved concrete schedule is `M=q+1`, `d=8M³`, `h=2π/d`,
`k=1/(6M⁴)`, `N=6M⁴`, reaching `T=1`. All seven new modules passed:
infinite reference, weighted tail, cutoff schedule, full error/convergence,
weighted error endpoint, common-time convergence, and ten exact controls.
The combined source has 70 new public audits and SHA-256
`8cbf781d91f3cd0cc5f6669586c55a4c4613d6f3e9f322e10fbafff39991e8c8`.
Both combined checks passed all 70 audits with only `propext`,
`Classical.choice`, and `Quot.sound`. The local check took 414.878 seconds
and completed at `2026-09-08T09:33:32.308259+00:00`; the independent check took
202.968 seconds and completed at `2026-09-08T09:32:08.453677+00:00`.

The previously available additional-check VM was lost during upload, before
its Exp009 proof check. Its receipts are retained in
`exp009/remote_check/lost_runtime/`. A new replacement CPU session is
`exp009-independent-check`, VM `m-s-kkb-usc1a1-d4w1b6hb9jym`, with clean root
`/content/exp009_check` and boot ID `99a6359d-eedf-49db-be73-d9b65de3bf31`.
The new VM independently downloaded its pinned compiler and libraries; all
57 bootstrap commands passed. The downloaded evidence passed validation:
91 payload hashes, 70 audits, six bootstrap inputs, and all 9,868 external
artifact hashes matched the accepted local records. All 21 targeted receiver
mutations were rejected. Evidence is saved under
`exp009/remote_check/downloaded_evidence/`; the final qualification is
`exp009/evidence/FINAL_VERIFICATION.json`.

The main result is
`e_N ≤ e_0 + sqrt(2*pi) * [T*(Ct(M)*k²+Cs(M)*h²)*A + 2*tail(M)]`,
where `A=sum norm(a_m)` is finite and both errors use the full infinite
Fourier reference. Weighted moments give `tail(M)≤A_r/(M+1)^r`.
This proves sampled grid convergence for the infinite Fourier evolution;
classical infinite-series PDE derivatives, variable spatial potentials, and a
universal second-order mesh rate for arbitrary infinite data remain outside
the result. Classical differentiation under sufficient coefficient regularity
is a natural next milestone.

Read `exp009/COMPLETION_REPORT.md`, `exp009/SAVED_FILES.md`, and
`exp009/REPRODUCE.md` for the accepted statements, checkpoints, and commands.
The verified numerical figure is `exp009/evidence/exp009_convergence.pdf`.
No proof checks remain running or required for Experiment 009.

Final packet: `/home/richman954/Exp009_Verified_Review_Packet_20260908.zip`.
SHA-256: `1ecbfe8203e1082ee8e89647e01a0c90aad3f366dcdc4dc797fea43d7b6d520c`.
All 193 payload hashes plus the exact manifest bytes and ZIP CRCs passed.
The external receipt is `exp009/evidence/FINAL_PACKET_RECEIPT.json`; a
neighboring `.zip.sha256` file records the archive checksum. The packet was
sealed at `2026-09-08T09:39:27.340304+00:00`.
All earlier sealed files remain unchanged. Initial source/archive pins are in
`exp009/evidence/BASELINE.json`.

## Experiment 010 completed and sealed

The user authorized the next milestone. Work is isolated in `exp010/`: the
infinite Fourier reference is now proved to be a classical periodic solution
under a summable second weighted coefficient moment. This includes actual
derivative existence, formulas and joint continuity, the pointwise equation
`iUt=-Uxx+(Z+X)U`, and the connection to sampled grid error and convergence
at time one. Read `exp010/COMPLETION_REPORT.md`.

The Exp009 combined foundation is copied unchanged; its pins are recorded in
`exp010/evidence/BASELINE.json`. New derivative diagnostics have passed.
All five new modules passed their modular Lean checks, including all three
derivative exchanges, the actual pointwise PDE, the explicit classical-solution
predicate, classical sampled grid error/convergence, and 18 exact controls.
An exact regular coefficient witness has nonzero support at every integer
frequency. Variable spatial potentials, uniqueness, interpolation convergence,
rougher coefficient classes, and a universal second-order mesh rate remain
outside the result.

A fresh CPU VM is initialized as `exp010-independent-check`, VM
`m-s-kkb-use1c1-1e742c6fpiifs`, boot ID
`aceca2e7-8363-4527-ad34-e11733e030af`, root `/content/exp010_check`.
Its initial project paths were empty; local receipts are in `exp010/remote_check/`.
The final combined source is `exp010/lean/Exp010Combined.lean`, SHA-256
`fb7b27b42d0baaca9ab8b30f9ba80bb0a5b8999986342fe8538e880bb3947ef0`.
Its 65 new public audits cover 47 production theorems and 18 controls.
Both combined checks passed all 65 audits with only `propext`,
`Classical.choice`, and `Quot.sound`. The local check took 376.693 seconds and
finished at `2026-09-08T10:27:35.092709+00:00`; the independent check took
282.011 seconds and finished at `2026-09-08T10:29:11.856806+00:00`.
The fresh VM's dependency bootstrap passed all 57 commands. Downloaded pinned
compiler and compatible library artifacts remain trusted inputs; project
artifacts were excluded from both final combined import paths.

Downloaded evidence in `exp010/remote_check/downloaded_evidence/` passed the
receiving validator: all 89 payload hashes, 65 audits, six bootstrap inputs,
57 command logs, and 9,880 cross-environment artifact hashes agree. The
independent archive SHA-256 is
`99fd76ab4d63e5ff8ce51d4f77ca6875f86260075a5672232298d6bb32e5ed49`.
Read `exp010/evidence/FINAL_VERIFICATION.json` for the accepted qualification,
`exp010/SAVED_FILES.md` for checkpoints, and `exp010/REPRODUCE.md` for reruns.

Final packet: `/home/richman954/Exp010_Verified_Review_Packet_20260908.zip`.
SHA-256: `91f4069711cc3ab26978d89eb9f12a2853524609e48d53c01e73eddbf74fd438`.
All 169 payload hashes, exact manifest bytes, and 170 ZIP members passed
readback/CRC validation. The packet was sealed at
`2026-09-08T10:30:09.097864+00:00`. Its external receipt is
`exp010/evidence/FINAL_PACKET_RECEIPT.json`, with a neighboring ZIP checksum.
All earlier sealed files remain unchanged. No proof checks remain running or
required for Experiment 010. The central resume file is outside sealed packets.

## Experiment 011 completed — independent VM validation accepted

The user asked to confirm independent Exp010 validation and proceed toward
the final goal. The accepted Exp010 VM identity, receipts, and all 169 sealed
payload hashes were rechecked successfully. The historical finite periodic
consistency/stability/convergence goal was already completed; later experiments
extend its scope. Read `WORKING_ROADMAP.md` for the current PDE direction and
the pending clarification about the separate inverse-integrator mission.

Experiment 011 is complete and isolated in `exp011/`. It proves uniform
convergence of explicitly reconstructed actual numerical spinor fields on
`[0,1] × [0,2π]` to the classical solution of `iUt=-Uxx+(Z+X)U`, under a
summable second weighted coefficient moment, exact sampled initialization,
and the proved growing-cutoff mesh/time schedule. Read
`exp011/COMPLETION_REPORT.md`, `exp011/MATHEMATICAL_DERIVATION.md` and
`exp011/SAVED_FILES.md` for the result, assumptions, evidence and checkpoints.
The finite reconstruction uses clamped floor indices and the last grid node
at the right spatial endpoint; finite fields may be discontinuous and need
not match at the two endpoints. The uniform bound covers that discrepancy.

All five new modules passed. Both combined checks passed all 44 new public
audits (29 production theorems and 15 exact controls), with only `propext`,
`Classical.choice`, and `Quot.sound`. The combined source SHA-256 is
`6e516d1a5cbd1eae23feddcb9b26a29c12a15a6a0d45928c891acd9be453e3e5`.
The local proof check took 420.470 seconds and finished at
`2026-09-08T11:33:54.319201+00:00`. The independent check took 304.076 seconds
and finished at `2026-09-08T11:35:11.151257+00:00`.

The independent CPU session is `exp011-independent-check`, VM
`m-s-kkb-usw3b1-3oqo9i5fec2ow`, boot ID
`3ee83a63-6560-4416-ac97-a34975a3e03e`, root `/content/exp011_check`.
Its initial project paths were empty and its VM identity differs from the
recorded predecessor VMs. The fresh dependency bootstrap passed all 57
commands. The compiler and compatible external libraries were downloaded
independently; they remain trusted inputs. No project build artifacts were
uploaded or used on either final combined import path.

The downloaded independent evidence passed the receiving validator: all 89
payload hashes, 44 audits, six bootstrap inputs, 57 command logs, and 9,880
cross-environment library artifact hashes agree. The independent archive is
`exp011/remote_check/exp011_independent_evidence_20260908T113556Z.tar.gz`, SHA-256
`a986cfb44931f34d433306697d961ee7407d058f14e9ca9ce5b8010065401a28`.
Read `exp011/evidence/FINAL_VERIFICATION.json` for the accepted qualification
and `exp011/REPRODUCE.md` for the preserved verification workflow.

Final packet: `/home/richman954/Exp011_Verified_Review_Packet_20260908.zip`.
SHA-256: `f6f52467bbed628201cc02f740a6203cb1b0ad57b3b257a8a89a1779e223cac3`.
All 179 payload hashes, exact manifest bytes, and 180 ZIP members passed
readback/CRC validation. The packet was sealed at
`2026-09-08T11:36:21.385029+00:00`. Its external receipt is
`exp011/evidence/FINAL_PACKET_RECEIPT.json`, with a neighboring ZIP checksum.
Earlier sealed experiment manifests and archive pins remain unchanged.
No proof checks remain running or required for Experiment 011.

The next analytic extension is uniqueness in the full classical periodic
solution class. The unverified feasibility probe is preserved with an explicit
interruption receipt and is excluded from production evidence. Spatially
varying potentials, weaker data, sharp rates, and the separate inverse-integrator
mission are outside the completed milestone. The central resume file and
working roadmap remain outside sealed packets.

## Experiment 012 completed — classical periodic uniqueness

Experiment 012 proves uniqueness in the unchanged
`Exp010.IsClassicalPeriodicSolution` class for `iUt=-Uxx+(Z+X)U`, period `2π`.
Any two classical solutions agreeing at one real time agree everywhere.
Energy conservation is derived from the actual PDE derivatives and periodic
flux; competing solutions need no Fourier representation. Regular Fourier
initial data admit exactly one classical solution, and the Experiment 011
reconstructed fields converge uniformly to it under the established data,
initialization and refinement assumptions. Read `exp012/COMPLETION_REPORT.md`,
`exp012/REPRODUCE.md` and `exp012/SAVED_FILES.md`.

All five modules and all 46 new combined audits (36 production results and
10 exact controls) passed locally and on a distinct fresh Colab CPU VM.
Only `propext`, `Classical.choice`, and `Quot.sound` were used. Combined SHA-256:
`ff98d87926fe6729202d77119d84e3ff3b3a3664ab607c0069a52db2c9f8547d`.
The local combined check took 454.824 seconds and finished at
`2026-09-08T12:40:03.639509+00:00`; the independent check took 287.927 seconds
and finished at `2026-09-08T12:39:53.915285+00:00`.

Fresh session: `exp012-independent-check`, VM `m-s-kkb-usw4c1-1loxz56gsupls`,
boot ID `a7a2db8d-794b-4bfb-8b4c-fbd00b5140ed`, root `/content/exp012_check`.
The completed Exp011 VM was released after explicit approval and preservation
checks; `exp012/remote_check/VM_REPLACEMENT.json` records the replacement.
The new VM started with empty project paths and independently downloaded
pinned compiler/library dependencies. All 57 bootstrap commands passed.
Project artifacts were excluded from both combined import paths. Lean and
compatible compiled libraries remain trusted inputs.

The downloaded independent evidence passed all 89 payload hash checks and
46 audit comparisons; 10,688 external artifact hashes agree across environments.
Archive: `exp012/remote_check/exp012_independent_evidence_20260908T124029Z.tar.gz`.
SHA-256: `44f6da9cf41fa9aabb1c3c7e6bbd16ba9dc5f8440adece252a0a1ed2a19498b5`.
The final review, verification and transfer receipts are preserved in `exp012/`.

Final packet: `/home/richman954/Exp012_Verified_Review_Packet_20260908.zip`.
SHA-256: `2c1347c1261c00f1f63e06b7c500235c48dfb5e9b817f25ffb23ea0edc0d596d`.
All 171 payload hashes and 172 ZIP members passed readback/CRC validation.
Sealed at `2026-09-08T12:46:12.221333+00:00`; external receipt:
`exp012/evidence/FINAL_PACKET_RECEIPT.json`. Earlier sealed files remain unchanged.
No proof checks remain running or required for Experiment 012.

The classical uniqueness gap for this concrete model is closed. Rougher data,
spatially varying potentials, other boundary conditions and sharp rates remain
extensions requiring their own scope. The active follow-up is recovery and
backup protection, recorded outside sealed experiments in
`/home/richman954/NDEA_Recovery/TASK_STATE.json` and `START_HERE.md`.

## Recovery and backup protection

The user's state-loss concern is addressed by verified recovery snapshots,
explicit task state, tested restore tools, and future-session instructions in
`/home/richman954/AGENTS.md`. Read `/home/richman954/NDEA_Recovery/START_HERE.md`
and `RECOVERY_POLICY.md`. Take `checkpoint.py --once` before long operations
and after milestones. A tracked watcher can save every minute while work is
active; there is no automatic reboot service. The failed detached launch was
detected, and a foreground run captured the completed packet successfully.

Recovery tests restored and verified 188 files; the independent review checked
all payload hashes and all eight active Lean sources. Later snapshots add final
receipts and notes and verify every captured payload. The completed release
bundle contains 40 selected packet/archive and checksum/receipt payloads through
Experiment 012, including explicit Exp003/004 archives and Git bundles. Its
actual restore and eight focused controls passed. Source originals are unchanged.
This bundle excludes historical intermediate files not explicitly listed.

Release bundle receipt: `/home/richman954/NDEA_Recovery/RELEASE_ARCHIVE_RECEIPT.json`.
Bundle SHA-256: `1f54a8205a6c26f354fff837de611ee910d148fd42e3e80b4722389360591f18`.
Latest checkpoint pointer: `/home/richman954/NDEA_Recovery/LATEST_CHECKPOINT.json`.
Both the release bundle and recovery snapshot were copied to the separate
`exp012-independent-check` Colab VM and checked there by SHA-256, byte count
and ZIP CRC. The exact current copied filenames/hashes are recorded in
`/home/richman954/NDEA_Recovery/OFF_MACHINE_BACKUP_RECEIPT.json`.

The current user preference is local Chromebook copies. The user canceled
Google Drive backup; do not mount Drive or resume its transfer unless newly
requested. There is no pending cloud backup task. For the local Chromebook copy, the accessible backup is recorded in
`/home/richman954/NDEA_Recovery/LOCAL_BACKUP_RECEIPT.json` when complete.
The main ChromeOS Downloads folder is not shared into Linux; local copies
are under Files → Linux files → Downloads. Do not claim a Drive copy exists.
Recovery snapshots preserve state and evidence; they are not new proof checks.

Verified local convenience backup completed: `/home/richman954/Downloads/NDEA_Backup_2026-09-08_132653Z_db972a`.
The folder contains the preserved release bundle, a recovery snapshot,
standalone restore utilities, README, task state and checksums (about 44 MB).
All copy hashes and both copied archive verifiers passed. The originals remain
unchanged. Open Files → Linux files → Downloads to find it.
See `NDEA_Recovery/LOCAL_BACKUP_RECEIPT.json` for the exact inventory receipt.
Google Drive backup was canceled by the user; local copies are the chosen destination.

## Experiment 013 in progress — generic energy and uniqueness

The user requested the next Lean step with broad mathematical reuse. Chosen
scope: generic complex Hilbert-valued classical periodic Schrödinger systems,
arbitrary positive period and space/time Hermitian potential, exact forcing
energy balance, homogeneous mass conservation, conserved same-forcing
L² distance and uniqueness. See `exp013/PLAN.md` and latest recovery task state.
The exact Exp012 combined foundation, all 171 predecessor payloads and its
sealed packet were verified before work. New source is not yet frozen or
claimed complete. Preserve all earlier releases. Local Chromebook backups
are the user-selected policy; Google Drive work is canceled.

Exp013 checkpoint: GenericClassical passed all 18 local theorems (169.483s)
and GenericEnergy passed all 13 integral/balance/conservation theorems
(204.159s). GenericUniqueness, LegacyBridge and exact controls remain under
verification. The fresh proof-check VM is `exp013-independent-check`, VM
`m-s-kkb-usc1c0-1k0px308tu45q`, boot `75274d51-536c-4a5f-a2de-f5814d0d098f`;
initial project paths were empty. No independent proof check is claimed yet.

Exp013 final-source freeze: all five modular checks passed, including 46 production
theorems and 18 controls. Combined SHA-256:
`d318bab32985465629249d7431061d6a3495e2bc5da5196fa740da253febde73`.
Exact deliveries are prepared; final review and local/fresh-VM combined checks
are next. No final combined result is claimed at this checkpoint.

Exp013 retry checkpoint: both first combined runs rejected an ambiguous
`smul_apply` in a control. Original source/deliveries and both failure logs
are preserved in `exp013/attempts/r1/`, with remote transfer hashes verified.
The explicitly qualified control passed again with identical compiled artifact.
Corrected combined SHA-256:
`b14e205da846e45c0ac506e9319a0f351e5148232ee4fc608193709734cd4788`.
The corrected local check is running; distinct fresh replacement session
`exp013-independent-check-r2` is bootstrapping, VM
`m-s-kkb-use1c2-3vyfjmsvu7xz8`, boot
`f7323458-d65c-4ed0-9889-e70929f24694`. Final success remains pending.

Corrected Exp013 local combined check passed 64 audits, exit 0,
602.710 seconds; source and external artifact hashes unchanged.
The fresh replacement VM is still checking the same corrected source.

## Experiment 013 completed and sealed

The reusable periodic Schrödinger framework is complete: arbitrary complex
Hilbert-valued classical solutions, pointwise selfadjoint space/time potentials,
exact forcing-work balance, homogeneous mass conservation, conserved distance
for shared forcing, and uniqueness for positive period. The legacy concrete
numerical convergence result is preserved through the exact predicate bridge.
General variable-potential existence and numerical convergence are not claimed.
Read `exp013/COMPLETION_REPORT.md` and `exp013/SAVED_FILES.md`.

The corrected combined proof passed all 64 audits (46 production declarations
and 18 controls), locally in 602.710 seconds and on the distinct fresh replacement
VM in 384.128 seconds. Only propext, Classical.choice and Quot.sound occur.
All 89 independent payload hashes,64 audit comparisons and 10,688 external
artifact hashes agree. Compiler and compatible external artifacts remain
trusted; project artifacts were excluded from both combined checks.
Original failed attempts are retained under `exp013/attempts/r1/`.

Corrected combined SHA-256:
`b14e205da846e45c0ac506e9319a0f351e5148232ee4fc608193709734cd4788`.
Independent evidence SHA-256:
`a53891735eec1e371e6eccb810498ebdb6d642ff131cc87517c0e9f94ee9c73b`.

Sealed packet: `/home/richman954/Exp013_Verified_Review_Packet_20260908.zip`.
SHA-256: `dbaad9c12c0f5154099f6ccaac3e1675fb6b678eb1ccb37d7f601e252dcf6412`.
All 313 payload hashes and 314 ZIP entries passed readback/CRC validation.
External receipt: `exp013/evidence/FINAL_PACKET_RECEIPT.json`.
No Exp013 proof check remains running or required. Predecessor manifests and
packets were preserved. Future research should start in a separate experiment.
The proposed next step is quantitative forcing/residual stability; it is
recorded in the roadmap and has not been started.

Final Chromebook convenience backup:
`/home/richman954/Downloads/NDEA_Backup_2026-09-08_150319Z_9a2eb2`.
All 18 copied file hashes passed; the copied utilities verified 333 recovery
payloads and 40 preserved release payloads. The separate Exp013 packet copy
matches its sealed checksum. Open Files → Linux files → Downloads.
The folder contains selected preserved releases through Exp012, the sealed
Exp013 packet, final working-state recovery, receipts and restore utilities.
No proof or backup action remains pending. The minute watcher stopped normally
after saving the final packet, and explicit snapshots preserved later notes.

## Experiment 014 active — general regular variable-potential existence

The user authorized proceeding toward general PDE existence. Target: global
classical existence and uniqueness on period 2*pi, arbitrary complex Hilbert
fiber, second weighted absolutely summable Fourier initial data and regular
selfadjoint variable potential. Construction uses a complete weighted Fourier
state, bounded convolution and a strongly continuous interaction-picture
linear evolution. No existence result is claimed yet. Read `exp014/PLAN.md`,
API reviews, newest modular receipts and recovery task state. All sealed
Exp013 payloads and its packet were reverified before work. A tracked minute
watcher is active in session20094, supplemented by manual milestone snapshots.

## Restart audit — September 8 evening EDT (September 9 UTC)

The Chromebook restart preserved completed Exp011–013 and active Exp014.
Fresh actual-result, transferred-evidence, sealed-payload and packet integrity
checks passed for Exp011–013 (44/46/64 audits in saved local/independent results).
The 15:55:43 UTC Exp014 checkpoint passed SHA-256 and all 100 payload checks;
all 11 captured Lean files match the live workspace. Four current modules have
successful receipts: StrongOperatorDerivative, GlobalLinearEvolution,
WeightedFourier and ScalarSeries. FourierPotential's 15:53:38 retry has no exit
code and an empty log; resume that check next. Later PDE/controls drafts remain
unchecked. No Exp014 final combined success or packet is claimed.

Colab CLI account access works; a fresh query found no active server sessions
and pruned four stale local records. A new CPU VM will be needed for independent
qualification. The previous HTTP412 allocation-limit receipt is historical;
no new allocation was attempted. Local compiler/pins and development artifacts
remain available. The old watcher/session IDs are stale. Status files now say
not running; restart and verify a tracked watcher when sustained work resumes.

The user requested a recap and a plan before proceeding. Read
`exp014/RESTART_PLAN.md` for exact receipts, interruption point, environment
status and the proposed sequence. This audit ran no Lean proofs and preserved
sealed sources. A new explicit checkpoint follows these note updates. The
verified Downloads convenience backup covers through completed Exp013, while
current Exp014 work is in separate local recovery checkpoints.

## Exp014 continuation — 2026-09-09T00:52:28.251860+00:00

The user authorized continuing after the ultimate-goal recap. The new tracked
minute watcher is session36928; startup and advancing timed snapshots were
verified. A fresh Colab CPU runtime exp014-independent-check is allocated
(VM m-s-kkb-use4c0-3g3ru54zvgn9o, boot e287ac86-e5ac-4c47-ba61-dc22f05b8e83),
with an empty initial project environment saved locally. Final bootstrap inputs
are not yet prepared. FourierPotential passed at the exact source recorded in
exp014/evidence/20260909T005013.187093Z_FourierPotential.json (78.768s).
Three restart failures caused by operator-space elaboration limits are preserved
under attempts/fourier_potential_restart_*; generic operator-series helpers
resolve them with the normal heartbeat budget. Synthesis/Product checking is
next, followed by ClassicalExistence and Controls. No final existence or
combined-check success is claimed yet.

Exp014 mathematical endpoint milestone (2026-09-09T01:19:44.466555+00:00): FourierSynthesis,
FourierProduct and ClassicalExistence now pass modular Lean checks with current
source/log/artifact hashes verified. The actual global_classical_exists_unique
theorem is accepted in the ClassicalExistence module; receipt
exp014/evidence/20260909T011651.939592Z_ClassicalExistence.json (93.673s, exit0).
Its original data/potential hypotheses remain unchanged. Exact controls and
final isolated local/fresh-Colab combined qualification are still pending;
there is no sealed Exp014 packet yet. Rejected drafts/logs are preserved.

Exp014 source freeze (2026-09-09T01:28:31.265335+00:00): all 9 modules passed with exact
source/log/artifact hashes verified, including 22 controls. Combined source
SHA-256 is 40d4c5fabfe49ad117ed5b442dd1e10f42a1fbf23afcc7b42a80ba9f5adb5aee,
with 143 new public audits (121 production and 22 controls). Exact bootstrap
and final-source deliveries are prepared and pinned. Final review and local/
fresh-Colab combined checks are next; no final qualification is claimed yet.

Exp014 local combined check passed all 143 audits, exit 0, in 178.418 seconds.
Only propext, Classical.choice and Quot.sound occur in the audit dependencies.
Source hashes and 10,768 isolated external artifact hashes remained unchanged.
The fresh Colab bootstrap/check remains pending; no final packet is sealed.


## Experiment 014 completed — global regular variable-potential existence

Experiment 014 constructs a unique global classical solution of
`i u_t = -u_xx + V(x)u`, periodic with period `2*pi`, for an arbitrary complete
complex Hilbert fiber. The prescribed initial coefficients `a(m)` and bounded
operator coefficients `v(m)` satisfy
`sum_m (1+|m|)^2 * norm(a(m)) < infinity` and the same weighted absolute
summability condition for `v`. Hermitian symmetry `v(-m)=v(m)*` makes the
time-independent potential `V(x)=sum_m exp(i*m*x)*v(m)` selfadjoint.

The construction retains all integer Fourier modes and covers every real
time. It establishes the actual time derivative, first and second spatial
derivatives, their joint continuity, periodicity and the prescribed initial
field. Uniqueness uses the unchanged Exp013 classical periodic predicate;
competing solutions need no Fourier representation. Exact controls include
a spatially nonconstant potential and regular data nonzero at every integer
frequency. Read `exp014/COMPLETION_REPORT.md`, `MATHEMATICAL_DERIVATION.md` and
`SAVED_FILES.md` for the endpoint, assumptions and evidence map.

All nine modules and both isolated combined checks passed. The combined audit
catalog contains 143 new declarations: 121 production results and 22 controls.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The local combined
check took 178.418 seconds and finished at `2026-09-09T01:32:12.815004+00:00`.
Combined source SHA-256:
`40d4c5fabfe49ad117ed5b442dd1e10f42a1fbf23afcc7b42a80ba9f5adb5aee`.

The independent CPU session is `exp014-independent-check`, VM
`m-s-kkb-use4c0-3g3ru54zvgn9o`, boot ID
`e287ac86-e5ac-4c47-ba61-dc22f05b8e83`, root `/content/exp014_check`.
Its initial project paths were empty and its allocation differs from the
recorded predecessor VMs. Both combined checks exclude project artifacts.
The pinned compiler and compatible external libraries remain trusted inputs;
they were not rebuilt from source. The combined source rechecks the three
retained generic Exp013 proof bodies and Exp014; earlier numerical chains
remain preserved in their own accepted packets.

The accepted qualification is `exp014/evidence/FINAL_VERIFICATION.json`;
the receiving evidence is bound by `exp014/remote_check/FINAL_TRANSFER_CHECK.json`.
`exp014/evidence/FINAL_PACKET_RECEIPT.json` identifies the sealed review archive
and exact packet checksum. Rejected development drafts and logs remain saved
under `exp014/attempts/` and `exp014/evidence/`. Preserve the sealed predecessors
and Exp014. Local Chromebook copies remain the chosen backup destination;
`NDEA_Recovery/LOCAL_BACKUP_RECEIPT.json` records the exact copied coverage.

This completes existence and uniqueness for the stated regular linear class.
Numerical convergence for spatially variable potentials is the next proposed
extension. Rough initial data, nonlinear equations, time-dependent potentials,
other boundaries and general convergence rates are outside this milestone.
No follow-on experiment has been launched by this completion note.

The independent check took 87.154 seconds and finished at
`2026-09-09T01:35:23.831616+00:00`. All 96 evidence payloads, 143 audits,
and 10,768 matching external artifact hashes passed receiving validation.
The CLI local connection record was restored to the same VM after a proxy
authentication error; boot identity matched and no proof rerun was needed.
Final packet: `/home/richman954/Exp014_Verified_Review_Packet_20260909.zip`.
SHA-256: `11aed98c23b9a5efc64e9f66d042d61ff08c1f33e76c4b8889174f299b56b282`.
All 262 payloads and 263 ZIP members passed hash/CRC/readback checks.
Final local convenience backup is complete; the final paragraph gives its folder and verified coverage.

Recovery metadata inclusion was corrected after the watcher stopped normally.
The restore/corruption/task-selection tests passed; the recovery ZIP now includes
the exact local-backup receipt, publisher and its tests. A286-payload snapshot
passed complete readback, including all four added metadata files.

Verified Chromebook backup completed at 2026-09-09T02:00:13.713893+00:00.
Folder: `/home/richman954/Downloads/NDEA_Backup_2026-09-09_015901Z_e51c03`.
All 21 copied-file checksums passed. Copied utilities independently verified
all 286 recovery payloads and 40 completed-release payloads. The publisher also
verified the supplemental Exp013 packet and exact Exp014 archive. Coverage is
contiguous through Exp014; earlier original archives remain unchanged.
`NDEA_Recovery/LOCAL_BACKUP_RECEIPT.json` holds the exact selection and hashes.
No proof checks remain running or required. The watcher stopped normally on
Exp014 completion; a final explicit checkpoint captures these notes and the
new backup receipt. Colab was used for independent checking; local files are
the selected permanent storage, and no Google Drive backup was performed.
The next residual/stability/convergence extension is proposed, not started.


## Experiment015 started — 2026-09-09T02:05:07.520698+00:00

The user authorized the proposed quantitative forcing/residual L2 stability
milestone. All262 sealedExp014payload hashes and its packet were reverified.
Its pinned combined source supplies the unchanged predecessor foundation.
Read exp015/PLAN.md. No Exp015 theorem or final result is claimed yet.

Exp015 progress at 2026-09-09T02:17:29.996011+00:00:
ScalarSqrtEstimate and ResidualField passed exact-source modular checks.
The scalar estimate keeps coefficient1 and handles zero energy by positive
regularization. ResidualField identifies the actual PDE residual and transfers
regular fields into the unchanged classical forced-solution predicate.
SpatialL2 is undergoing local elaboration fixes; final PDE-error and control
modules await its accepted build. No combined/final Exp015 claim is made.
The new tracked watcher94110 produced startup and advancing timed snapshots.
Fresh ColabCPU exp015-independent-check (VMm-s-kkb-ass1a0-1gts16oqjjhbw,
bootbb7ce4d2-8e5b-4960-9ba7-5dd6feb82daa) has empty initial project paths,
with the exact environment receipt downloaded locally before proof inputs.

Exp015 main inequality passed at 2026-09-09T02:26:32.029328+00:00:
`classical_forcing_stability` in ForcedStability.lean is accepted at its exact
source, preserving arbitrary initial error and coefficient1. Its modular check
exited0 with an empty log in137.770s; receipt
`exp015/evidence/20260909T022244.427691Z_ForcedStability.json`.
Residual/Exp014 specialization/control checks and final combined qualification
remain pending; this is not yet a sealed experiment.

Exp015 full mathematical endpoint passed at 2026-09-09T02:35:36.326334+00:00:
all six production modules now have successful exact-source receipts, including
VariablePotentialBridge in270.039s with an empty log. The residual estimate
applies to Exp014.solution under its original regular potential/Fourier-data
hypotheses and retains both arbitrary initial error and exact initialization.
The22exactcontrols and final local/fresh-Colab combined qualification remain
pending; no Exp015packet is sealed yet.
