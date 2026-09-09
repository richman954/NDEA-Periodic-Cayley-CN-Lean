# RAM shadow-source provenance

The modular run compiled the actual Step 2 production and control files. Their
predecessor `.olean` inputs were rebuilt in RAM from shadow files whose theorem
bodies are byte-identical to the immutable sources from the first `/-!` module
documentation marker onward. Three independent `cmp` commands returned exit
code 0 for those body suffixes.

The complete source diffs contain import changes only:

1. `OperatorCayley.lean` removes the umbrella `import Mathlib`, retains
   `Mathlib.Analysis.CStarAlgebra.Matrix` and `Mathlib.Tactic.NoncommRing`, and
   explicitly adds Matrix Hermitian/PosDef plus Module/NormNum/Ring tactic
   imports.
2. `EuclideanResolventContraction.lean` retains its OperatorCayley import and
   explicitly adds FinCases/Module/NormNum/Ring tactic imports.
3. `AdversarialWitnesses.lean` retains its OperatorCayley import and explicitly
   adds FinCases/NormNum/Ring tactic imports.

No declaration, theorem statement, proof term, namespace, notation, or audit
command differs after the import block. The shadow files are verification
infrastructure only. The release claim is therefore: actual Step 2 sources
compiled against freshly rebuilt, body-identical predecessor modules with
explicit narrow imports. It is not a claim that the immutable predecessor files
themselves were freshly compiled through their broad umbrella import.
