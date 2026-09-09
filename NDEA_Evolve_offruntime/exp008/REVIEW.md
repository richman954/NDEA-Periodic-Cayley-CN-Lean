# Experiment 008 review

Reviewed September 8, 2026. This is a read-only mathematical and verification-design review, **not a combined-verification result**. No Lean compilation was run for this review. Accepted completion still requires the final local and independent combined receipts, transfer/integrity checks, and release checks.

Reviewed: `PLAN.md`, `MATHEMATICAL_DERIVATION.md`, `lean/SuperpositionClosure.lean`, `lean/StageBridge.lean`, `lean/Controls.lean`, `make_combined.py`, and `verify_combined.py`; supporting definitions, the axiom-log checker, and dependency-copy helper were inspected where needed.

## Mathematical findings

No mathematical blocker was found in the reviewed statements and proof chain.

- **Actual sampled PDE:** `superposition_is_sampled_solution` identifies every grid coordinate of the lifted orbit sum with `finiteSolution` evaluated at the corresponding physical site. The grid evolution uses the actual full-grid symmetric Cayley operator. The reference is a finite continuum Fourier sum, not an assumed grid trajectory.
- **Arbitrary initialization:** `finite_superposition_grid_error` permits every initial grid vector. Full-grid unitarity preserves its entire discrepancy from the sampled reference, including frequencies outside the chosen reference spectrum.
- **Derived residual budget:** `frequency_stageResidualBudget_bound` derives the third denominator residual from the independently proved complete-step defect and the `9/8` denominator bound. The first two residuals vanish because their auxiliary states are actual Cayley stages. `actual_superposition_stage_budget` lifts these exact residuals and applies discrete Parseval. It assumes mesh, cutoff, and timestep conditions; it does not assume the residual estimate being claimed.
- **Proof dependency distinction:** the global error endpoint is proved directly through unitary power estimates and Parseval. The actual three-stage residual bound is also proved; the global endpoint does not invoke that residual theorem as an intermediate premise.
- **Fixed-cutoff convergence:** `M`, `S`, coefficients, and the horizon are fixed outside the refinement index. Mesh identity, `d>2M`, `Mh≤1`, and the timestep restriction are explicit hypotheses for every mesh in the family. The endpoint concerns weighted grid errors at the actual times `Nk≤T`; it does not assert terminal-time convergence to `T`, a growing cutoff, or arbitrary infinite Fourier data.
- **Controls:** the signed spectrum has three nonzero coefficients and nonzero physical initial data. The alias witness uses frequencies `0` and `d` with opposite coefficients and demonstrates why unrestricted Parseval fails. The remaining controls cover an admissible positive-step mesh, retained initial error, the noncommuting split, and explicit frequency dependence of the constants.

## Public theorem audit coverage

An independent declaration inventory agrees with the in-memory combined-source reconstruction: **90 new public theorems, consisting of 83 production theorems and 7 controls**.

| Module | Public theorems |
|---|---:|
| FrequencyBounds | 15 |
| ContinuumModes | 25 |
| FourierGrid | 13 |
| Orthogonality | 12 |
| SuperpositionClosure | 10 |
| StageBridge | 8 |
| Controls | 7 |
| **Total** | **90** |

The current catalog includes attributed public declarations. Private helpers are excluded from this count and are covered transitively when used by audited theorems. The frozen predecessor source is re-elaborated in the combined file; these 90 audits count only the new Experiment 008 public results. The exploratory `OrthogonalityProbe.lean` is correctly excluded from production ordering.

## Verification design and trust boundary

The final checker reconstructs the combined source and complete audit catalog, checks source/compiler/helper pins, restricts imports to external modules, copies a dependency closure into an isolated library, checks a successful compiler exit and exact axiom-log coverage, and compares project-source and copied-artifact hashes after the run. Allowed axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

One wording correction was requested: the verifier initially described reused external artifacts as “pinned.” Its checks pin dependency source commits and record/stability-check the copied artifact bytes; they do not prove that those cache bytes were built from those source commits. Compatible external cache provenance and the Lean toolchain, including the core library used by `LEAN_PATH`, remain trusted inputs. This is consistent with the boundary already stated in `PLAN.md`.

Correction status: **addressed**. The verifier header now says “recorded compatible external artifacts”; its recorded scope explicitly states that the compiler/library artifacts remain trusted and that this check neither rebuilds them nor proves source-to-artifact correspondence. Both edited lines were rechecked. Final combined acceptance remains pending the verification receipts.


## Final evidence transfer review

A further read-only review covered `prepare_final_sources.py`, `remote_check/export_evidence.py`, `remote_check/check_export.py`, and the final verifier. The upload launch helper was inspected to trace the complete input identity chain. Archive member checks, full export-manifest coverage, combined-source identity, and independently re-parsed axiom-log checks are consistent with faithful transfer. All four reviewed Python files parsed successfully without executing a verification or transfer.

One concrete gap was identified and **addressed** in the receiving checker: it now compares the returned `FINAL_TRANSFER_INPUTS.json` with the local upload catalog, checks every uploaded verification input against both the returned bytes and current local bytes, and requires the reported executed-verifier hash to equal the uploaded verifier hash. The added checks were re-read and confirmed. This closes the reviewed identity gap for verifier/helpers as well as Lean source. No remaining transfer-design blocker was found. Actual combined verification and evidence-transfer acceptance still require their final successful receipts.

## Subsequent accepted evidence

The pending statements above record the review-time checkpoint. Both combined
checks subsequently passed all 90 audits, and the transfer checker accepted all
138 exported file hashes plus the uploaded verification-input identity chain.
The final qualification and matching modular/combined receipts are in
[FINAL_VERIFICATION.json](evidence/FINAL_VERIFICATION.json). All 9,868 external
artifact paths and hashes agree between the environments. This later evidence
completes the checks that were pending when the design review was written.

## Packet sealing review

The final sealer was reviewed before packaging. It binds current verifier,
generator, helper, and lockfile bytes to the uploaded input catalog, and binds
accepted compiler logs and dependency manifests to each combined result.
It checks exact manifest bytes both inside the ZIP and on disk, verifies every
payload hash and archive CRC, and preflights exclusive output creation to
preserve existing packets. The identified gaps were corrected and rechecked;
no remaining sealing blocker was found. The actual outcome is recorded in the
external `evidence/FINAL_PACKET_RECEIPT.json` after the ZIP is written.
