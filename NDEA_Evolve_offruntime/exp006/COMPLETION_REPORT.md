# Experiment 006 — verified locally and independently on Colab

The concrete periodic-mode milestone is complete. Experiment 005's actual
three-stage residual premise is now derived for

\[
U(t,x)=e^{i(x-2t)},\qquad iU_t=-2U_{xx},\qquad x\in\mathbb R/(2\pi\mathbb Z).
\]

Both split generators are active copies of the negative Laplacian. The
discrete matrices use the actual cyclic centered difference, with the two
periodic endpoint wraps proved explicitly.

For a `d`-point grid with `d*h=2*pi`, `0<h<=1`, and `0<=k<=2`, the actual
unscaled factor residuals satisfy

\[
\operatorname{stageResidualBudget}
\le k\sqrt{2\pi}\left(\frac{5}{16}k^2+\frac14h^2\right).
\]

Consequently, for `N*k<=T`,

\[
e_N\le e_0+T\sqrt{2\pi}\left(\frac{5}{16}k^2+\frac14h^2\right).
\]

The scalar mesh-weighted error also tends to zero when mesh spacing, time
step, and initial weighted error tend to zero under a common time horizon.
These concrete endpoints do not assume the residual bound they establish.

## Verification

| Check | Result |
| --- | --- |
| New local production modules and controls | Passed |
| Local combined proof with project artifacts excluded | 41/41 audits; exit 0; 161.608 seconds |
| Independent Colab combined proof with project artifacts excluded | 41/41 audits; exit 0; 141.621 seconds |
| Coverage | 35 production theorems and 6 exact controls |
| Axioms | Only `propext`, `Classical.choice`, and `Quot.sound` |
| Source integrity | Same combined SHA-256 locally and remotely; unchanged during both checks |
| Independent dependencies | Pinned compiler and libraries downloaded on Colab; 9,868 dependency artifact hashes checked unchanged |
| Evidence transfer | Archive checksum and all 22 evidence-file hashes passed; all 41 audits matched the local expected names |

The compiler is Lean 4.31.0 and Mathlib is pinned to
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. Compatible compiled library
artifacts are trusted inputs; Lean and Mathlib themselves were not rebuilt
from source. The combined proof includes and rechecks the frozen predecessor
source, and does not import project build artifacts.

The scope is one nonzero Fourier mode on a fixed period and two commuting
split operators. Arbitrary smooth data, noncommuting operators, variable
potentials, interpolation convergence, and sharp constants remain outside
this result. Experiment 005 was preserved without changes.

## Sources and evidence

- [Concrete matrix proof and convergence endpoints](lean/Exp005ModeBridge.lean)
- [Mathematical derivation](MATHEMATICAL_DERIVATION.md)
- [Local verification report](evidence/FINAL_VERIFICATION.json)
- [Independent verification report](remote_check/final_evidence/final_verification/RESULT.json)
- [Independent compiler log](remote_check/final_evidence/final_verification/combined.log)
- [Local transfer audit](remote_check/FINAL_TRANSFER_CHECK.json)
- [Convergence figure, PDF](remote_check/final_evidence/convergence/exp006_convergence.pdf)

The numerical figure and the 147 stage/49 trajectory checks are supporting
floating-point diagnostics. The finest plotted observed order is 1.9999.

Combined proof SHA-256:
`af3d14716b492f6485dd1bcf88c3c99cd13440a219f89b27b5258531d7f96c52`.

Independent evidence archive SHA-256:
`2f7b33ec4f5902bfac0cbe25b3a50978519cc96a7048da86a6e3aa164a814f0a`.

The dated `STATUS_FINAL_LOCAL_GREEN.md` and its 21-entry manifest are retained
unchanged; this report records the subsequent independent completion.
