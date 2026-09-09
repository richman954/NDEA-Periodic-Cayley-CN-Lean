# Proposed first affine reconstruction module

Status: first foundational module locally accepted. All 14 theorem declarations elaborated with exit code 0; combined axiom audit and independent Exp016 qualification remain separate work. This is a reusable algebra/regularity interface, not a convergence theorem.

For a complex Hilbert space H and two spatial profiles a,b : ℝ → H, define θ(t)=(t−t₀)/k and w(t,x)=a(x)+θ(t) • (b(x)−a(x)), with real scalar action. Its global affine extension avoids claiming differentiability across time-step junctions. A later piecewise reconstruction must handle those junctions separately.

Each endpoint profile is assumed differentiable in space, with differentiable first derivative, continuous second derivative, and period L. A four-field IsRegularPeriodicProfile packages precisely these premises. There is no sign/positivity assumption on L in this regularity algebra. k≠0 is needed to identify the right endpoint t₀+k; derivative/algebra formulas themselves also hold under Lean's total division convention when k=0.

The intended accepted statements are:

- w(t₀,x)=a(x), and w(t₀+k,x)=b(x) for k≠0.
- ∂ₜw(t,x)=k⁻¹ • (b(x)−a(x)).
- ∂ₓw=a′+θ • (b′−a′), and ∂ₓₓw=a″+θ • (b″−a″).
- Joint continuity of the field and those actual derivatives, plus spatial periodicity, establishing the existing Exp015.IsRegularPeriodicField L w.
- For the actual Exp015.pdeResidual, the exact identity R(V,w)(t,x)=i • (k⁻¹ • (b−a)) + a″+θ • (b″−a″) − V(t,x)(a+θ • (b−a)). No assumed residual-smallness premise is introduced.
- A real-linear synthesis J : E →ₗ[ℝ] (ℝ → H) sends the actual affine state q₀+θ • (q₁−q₀) to this field with a=Jq₀ and b=Jq₁. No norm or continuity of J in the state variable is needed for this finite affine identity; regularity is explicit for the two synthesized spatial profiles. A complex-linear synthesis can be restricted to real scalars.

The actual existing recurrence is the symmetric A-half/B-full/A-half split. Affine time reconstruction is not asserted to preserve its second-order accuracy: its residual may only support a first-order estimate. A quadratic correction should be compared before choosing the final reconstruction. Arbitrary endpoint profiles are retained, with no exact-initialization premise; the left-endpoint identity preserves whatever initial mismatch is present.

The exact midpoint CN/stage equation can later rewrite the time-slope term and isolate discrete/spatial consistency terms. Choosing the actual scheme, proving that algebraic stage relation, proving quantitative residual bounds, and deriving variable-potential discrete convergence are outside this first module.

Implementation target: exp016/lean/AffineReconstruction.lean, namespace NDEAEvolve.Exp016, importing accepted ResidualField. Existing accepted files remain unchanged. The original Exp015 runner uses pinned Lean 4.31.0, separate experiment build directories, all necessary predecessor build paths, and /tmp/exp003_lean_one_job.lock. Root supplied the new pinned runner and confirmed the advancing recovery watcher and explicit draft checkpoint before compilation. The active runner uses the same shared lock and preserves complete compiler logs.

Accepted predecessor readback: Exp015 final verification passed with 50 audits, combined SHA256 ef99d7098209d790f32abf89e2ec866e1b3c0cb2ce5b4262022df3cfdbf18846. FINAL_VERIFICATION.json SHA256 fc9c6dc0930bbc458955fe71d9864dbd729bba65efdeb9cafe63476ba0f49962; FINAL_PACKET_RECEIPT.json SHA256 6a2cabb60c3b5f200c55b55517119b94ee5885a7006ebc5f3b22c3c80ba5867e. Those establish the predecessor, not this proposed module.

## Local module acceptance

Accepted receipt: evidence/20260909T042218.136527Z_AffineReconstruction.json. Elaboration took 355.338778384 seconds after acquiring the shared compiler lock. The only diagnostics were seven linter.unusedSectionVars warnings for CompleteSpace H; no errors. Source SHA256 c12486b6d86a23b3f6084f73ff283da756ea8d1ae3b72659babe85b2359654cf; full compiler log SHA256 86fb0f4707e077b308a52e2f4f9c21c84255e55c7f364a073b59bfd80e2175bb; compiled output SHA256 75044f1d402bab4328728de1bfaa45d7242fa6beb046c5c0b61a0aec591578a6. The source, runner, pinned compiler, log and output hashes were rechecked against the accepted receipt. The direct ResidualField and GenericClassical source/output hashes still match their accepted predecessor receipts.

The rejected first draft is preserved in probes/affine_first_failed/AffineReconstruction.lean, with receipt evidence/20260909T041022.558189Z_AffineReconstruction.json and its full log. Its sole error was scalar real-module elaboration in affineTimeWeight_hasDerivAt. The correction gave an explicit real lambda target and used expected-type elaboration (`using!`); all theorem statements and assumptions remained unchanged. No heartbeat budget was raised.

A downstream per-step consumer can apply Exp015 to each slab's globally affine extension and telescope endpoint errors. This uses the exact endpoint identities without imposing global differentiability across time-step junctions. It does not establish a residual bound or convergence rate by itself.
