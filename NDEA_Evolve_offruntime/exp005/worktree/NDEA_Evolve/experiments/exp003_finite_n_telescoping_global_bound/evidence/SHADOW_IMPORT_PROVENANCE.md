# RAM shadow-source provenance

The qualifying modular run compiled the actual immutable Step 2 and Step 3
production modules, the actual Step 4 production module, and the actual Step 4
controls. The Exp002 Cayley and Step 1 predecessor `.olean` inputs were freshly
rebuilt in RAM from the narrow-import shadow files already audited and released
with Step 2.

Current body-suffix comparisons from the first module documentation marker
return exit code 0. Full diffs show import-block changes only:

1. `OperatorCayley.lean` replaces the umbrella `import Mathlib` with explicit
   Matrix, Hermitian, PosDef, NoncommRing, Module, NormNum, and Ring imports.
2. `EuclideanResolventContraction.lean` retains its OperatorCayley import and
   adds explicit FinCases, Module, NormNum, and Ring imports.

No declaration, theorem statement, proof term, namespace, notation, or audit
command differs. The release claim is that actual Steps 2–4 compiled against
freshly rebuilt, body-identical predecessor modules with explicit narrow
imports; the immutable broad-import predecessor files were not rebuilt or
edited in place.
