# Renewed-window repair probes

These files are assurance probes, not production Lean sources. They preserve the
smallest-check sequence used before rebuilding the repaired strengthened witness.

| Probe | Outcome | Interpretation |
|---|---|---|
| `WrongSignRepairProbe.lean` | exit 1 | Import/build-order failure: the production witness `.olean` did not yet exist. Not a mathematical result. |
| `WrongSignRepairProbeV2.lean` | interrupted; result not obtained | Import-heavy exact specialization produced no diagnostic before manual interruption. No exit code was captured and none is inferred. |
| `EqNegSelfAlgebraProbe.lean` | exit 1 | Harness import was too narrow to make the generic module class available. Not a proof result. |
| `EqNegSelfAlgebraProbeV2.lean` | exit 124 | Bounded five-minute timeout while loading the Exp002 core; no Lean diagnostic. Not a proof result. |
| `EqNegSelfAlgebraProbeV3.lean` | exit 1 | Useful proof diagnosis: the generic cancellation argument requires a torsion-free module. |
| `EqNegSelfAlgebraProbeV4.lean` | exit 0 | The repaired localized `congrArg` argument passes with `Module.IsTorsionFree ℂ V` explicit. |

The exit-0 V4 result validates only the algebraic repair. The concrete theorem
`pauli_cayley_commutator_wrong_sign` remains untested until the complete production
`AdversarialWitnesses` module succeeds. Authoritative machine-readable timing records
and logs live under `evidence/metadata/`, `evidence/logs/`, `metadata/`, and `logs/`.
