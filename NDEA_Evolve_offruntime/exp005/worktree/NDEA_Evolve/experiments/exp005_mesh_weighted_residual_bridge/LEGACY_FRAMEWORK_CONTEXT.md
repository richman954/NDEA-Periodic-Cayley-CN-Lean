# Read-only context from the periodic-grid project

The following files were inspected under
`/home/richman954/NDEA/workspace/NDEAMathlibGate/NDEAMathlibGate/`.
They are not imported by Exp005 and were not edited. These hashes identify
the inspected context; they are not a new compilation or release audit of
the legacy project.

| File | SHA-256 at inspection |
| --- | --- |
| FiniteStateEuclideanNormBridgeV1.lean | 2e8022ef5c6edce94b2f54dfa25bfc99112a8c13b4a7ca8269ece0d6bfe4477e |
| WeightedCayleyGlobalErrorV1.lean | 1c6dc040337debd861a08777aa0838b1415c4e7c23fcfe5a01026447b5b35a79 |
| PeriodicSpaceTimeVectorConsistencyV1.lean | fb9cccb5c081659c12d517afe4b1cee942d9055127985da7ee1dbdae50bd9a25 |
| PeriodicCayleyCNAnalyticClosureV1.lean | 35c7b20e2128b7c685e5265b219eb5af567e47c1420209723529836611e54b2e |

The legacy weighted quantity is sqrt(dx) times the norm on
`EuclideanSpace ℂ (Fin n)`, exactly the formula reused here. Its accumulation
and analytic-closure theorems concern a single unsplit Cayley/CN update.
The analytic closure supplies a consistency estimate for a supplied smooth
periodic free-Schrödinger solution with stated space/time derivative bounds;
it is not a general symmetric splitting consistency theorem.

Exp005 reestablishes the required weighted stability and accumulation in
the maintained Exp002–004 representation and proves the three-stage factor
bridge. This avoids importing the broad historical stack while keeping the
mathematical compatibility explicit. A formal theorem identifying the two
separate projects' declarations is not claimed.
