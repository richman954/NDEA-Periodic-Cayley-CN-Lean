# Experiment 015 — quantitative forcing and residual stability

Status: completed and verified. See [COMPLETION_REPORT.md](COMPLETION_REPORT.md).

User authorization: “good call, proceed”, following the proposed Exp015 residual-to-error milestone.

Target: for classical periodic Hilbert-valued Schrödinger fields u and v with
a common pointwise selfadjoint potential, period L>0, and sufficiently regular
forcing difference, prove for s<=t:

    ||u(t)-v(t)||L2 <= ||u(s)-v(s)||L2 + integral_s^t ||f(r)-g(r)||L2 dr.

Use the unchanged Exp013 classical predicate and its actual energy derivative.
Take joint continuity of the forcing difference as an explicit initial scope;
prove the spatial/time integral prerequisites. Handle zero error by a positive
square-root regularization before its parameter tends to zero. The coefficient
one and the exact-initialization case are required. Define a classical regular
approximate field and its actual PDE residual, derive the residual estimate,
and specialize to the unique regular static variable-potential solution from
Exp014. Include initial-error preservation, zero-defect, exact initialization,
and an active forcing control. This is an L2 stability milestone; convergence
of actual discrete iterates/reconstructions remains a later experiment.

Modules: ScalarSqrtEstimate, SpatialL2, ResidualField, ForcedStability, ResidualEstimate,
VariablePotentialBridge, Controls. Sealed Exp014Combined bodies provide the
pinned predecessor foundation. No sealed predecessor edits are permitted.

Completion gates: exact-source module checks; independent source/tool review;
isolated local combined check; distinct fresh-Colab qualification with pinned
external inputs; complete downloaded evidence validation; sealed review packet;
verified local Chromebook backup and final continuity checkpoint. Compiler and
compatible library artifacts remain trusted inputs. Drive backup is canceled.
