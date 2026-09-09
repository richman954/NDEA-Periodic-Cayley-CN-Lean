# Julia certificate and independent validation

The Julia 1.12.6 discovery stage used exact rational/Gaussian-rational matrix
arithmetic only. It checked five exact cases, inverse and identity residuals,
zero and negative steps, the commuting nonzero defect, the corrected
large-step control, and a free noncommutative word-polynomial expansion.

Canonical identifiers:

- run ID: `exp003-step3-027927a54ca8669413576cc8`;
- core SHA-256:
  `027927a54ca8669413576cc8c9811e1e1485ff4fb81e67a8046581f0bc0acdbd`;
- certificate SHA-256:
  `fa80da1701893081d6fc780f80345d357dcc9de829a6d450d7e5c679955ba3c0`;
- generated receipt SHA-256:
  `aac451cc2f734dfad981cd3af9ca134e0a9d7f5e4a4daf37465f028f8f4ec9b8`.

The certificate contains exact input matrices, Cayley denominators and
inverses, residual matrices, local defects, factorized targets, the formal
noncommutative derivation, source hashes, and explicit claim boundaries. Its
schema is `ndea.exp003.step3.split_unsplit_certificate.v1`.

The Python 3.11 validator does not invoke Julia. It parsed the certificate,
reconstructed every rational and Gaussian-rational value using
`fractions.Fraction`, recomputed canonical hashes, repeated all matrix and word
polynomial checks, validated source and receipt bindings, and passed 407 checks.

The finite certificate is discovery and cross-language evidence. It does not
claim universality. The arbitrary-matrix identity and operator-norm theorem are
certified independently by Lean.
