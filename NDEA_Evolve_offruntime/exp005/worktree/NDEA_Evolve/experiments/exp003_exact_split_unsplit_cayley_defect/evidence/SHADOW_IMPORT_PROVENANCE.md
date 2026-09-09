# RAM shadow-source provenance

The qualifying modular run compiled the actual immutable Step 2 production
module, the actual Step 3 production module, and the actual Step 3 controls.
The Exp002 Cayley and Step 1 predecessor `.olean` inputs were freshly rebuilt
in RAM from the narrow-import shadow files already audited and released with
Step 2.

Current `diff -u` checks show that each shadow differs from its immutable
source only in the import block:

1. `OperatorCayley.lean` removes the umbrella `import Mathlib`, retains its
   Matrix and NoncommRing imports, and adds explicit Hermitian, PosDef, Module,
   NormNum, and Ring imports.
2. `EuclideanResolventContraction.lean` retains its OperatorCayley import and
   adds explicit FinCases, Module, NormNum, and Ring imports.

No declaration, theorem statement, proof term, namespace, notation, or audit
command differs. The shadows are verification infrastructure only. The release
claim is therefore that the actual Step 2 and Step 3 files compiled against
freshly rebuilt, body-identical predecessor modules with explicit narrow
imports; it is not a claim that the immutable broad-import predecessor files
were recompiled in place.
