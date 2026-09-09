
# NDEA-Evolve Experiment 001: goal and success contract

The goal is an audited Julia → Lean discovery-and-verification pipeline for
Fourier-mode stability of the periodic one-dimensional centered negative discrete
Laplacian with a Cayley–Crank–Nicolson scalar update.

For a periodic phase mode, the experiment must reconstruct

`lambda_h(theta) = (4 / h^2) * sin(theta/2)^2`

and

`G(theta) = (1 - i*(k/2)*lambda_h(theta)) / (1 + i*(k/2)*lambda_h(theta))`,

then establish `|G(theta)| = 1` with explicit real-parameter and grid-spacing
assumptions. Julia must emit auditable exact and numerical evidence; Lean must
prove the general result independently; false variants must be rejected; and the
complete evidence must be hash-manifested and reproducible.

This workspace is additive and never recreates or overwrites the lost immutable
baseline evidence directory. The known baseline identities remain references in
`metadata/baseline_reference.txt`.
