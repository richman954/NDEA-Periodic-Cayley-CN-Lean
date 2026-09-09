# Experiment 015 infrastructure implementation review

Status: adaptation and offline checks passed. This is the implementer's review
of the verification protocol; final independent source/tool review and all
proof-completion receipts remain required.

The foundation is pinned to the entire accepted Exp014 combined source.
Reconstruction deletes only its 143 old axiom-print commands and checks the
result against the fixed foundation hash. Every predecessor theorem body is
retained. All seven new source modules contribute public theorem/lemma names;
comments and private declarations are excluded, duplicate names are rejected,
and new public names must belong to NDEAEvolve.Exp015. Final counts are derived
from the completed source rather than copied from Exp014. Unexpected project
imports and changed predecessor/foundation bytes stop preparation.

The local/fresh combined checker uses pinned compiler and dependency sources,
an isolated external artifact closure and a source containing only external
imports. It removes inherited source/core overrides, replaces LEAN_PATH, rejects
project artifacts and checks source/dependency hashes before and after compiling.
Compiler and compatible library binaries remain trusted inputs; source-to-binary
correspondence and fresh compiler/library builds are outside the qualification.

Bootstrap deliveries are exact source-only archives, read back before their
launcher is pinned. Fresh initialization records an empty project environment.
The receiver requires a distinct VM and boot identity, including rejection of
the accepted Exp014 identity, exact bootstrap input bytes, completed command
logs, pinned source checkouts and matching compiler/library artifacts. It checks
chronology only within the remote VM's clock domain. Parent and remote clocks
need not agree. The source launcher requires successful bootstrap for the same
combined source and refuses existing work directories.

Evidence validation happens before extraction. Archive SHA-256, canonical
regular unique members, bounded payload size, complete manifest coverage,
source delivery bytes, both compiler audit logs and dependency maps are checked.
Only then can an accepted transfer receipt bind exact local/independent files.
Finalization requires this receipt, fresh-bootstrap success, source/tool/document
review, current successful modular source/log/artifact hashes and unchanged
predecessor manifests. It refuses existing sealed output and verifies complete
ZIP readback, CRC and all payload hashes before writing the packet receipt.

Offline tests use synthetic source and archive fixtures plus explicitly
transformed predecessor bootstrap evidence. They exercise reconstruction,
namespace/import/corruption rejection, delivery repeat refusal, fresh identity
checks and environment isolation. They create no real Colab session and their
fixtures are never accepted as new mathematical proof evidence. Saved test
receipts identify the executed test source. Final independent review should
check those receipts and the exact current scripts before freezing deliveries.

The saved offline results cover 12 foundation/catalog controls in
`evidence/COMBINED_INFRASTRUCTURE_TESTS.json`, 26 source-delivery/archive/bootstrap
controls in `evidence/INFRASTRUCTURE_TESTS.json`, five inherited-environment
controls in `evidence/ENVIRONMENT_ISOLATION_TEST.json`, and 19 finalizer rejection
controls in `evidence/FINALIZER_GATE_TESTS.json`. The finalizer fixtures relocate
only the archive destination and require rejection at the intended gate without
any file change. They include altered accepted bytes, absent review coverage,
unreviewed tools/documents and missing modular proof after prior fixture gates.

The qualification and generated report concern coefficient-one continuous
L2 forcing/residual stability and its Exp014 application. They do not claim
convergence or rates for discrete iterates/reconstructions. Recovery/backup
operations are managed outside the sealed experiment, using local Chromebook
copies; no cloud-backup operation is performed by these tools.
