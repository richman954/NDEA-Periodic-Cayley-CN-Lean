# Experiment 014 verification infrastructure review

Independent read-only review performed on 2026-09-09 UTC while modular proof
checks were still in progress. The only file written by this review is this
document. No Lean check, bootstrap, transfer, packaging operation, or unchanged
infrastructure test was rerun. This is a workflow review, not an accepted final
proof result or a substitute for the exact final-source review.

No acceptance-gating blocker was found in the reviewed implementation. The
final frozen review below now covers the prepared deliveries and their actual
launcher pins. The local combined result has since passed; independent
combined verification, downloaded-evidence validation, and packet sealing
still require their own accepted receipts. See `REVIEW.md` and
`evidence/REVIEW_CHECK.json` for the exact final source/document bindings.

## Existing evidence and scope

The saved `evidence/INFRASTRUCTURE_TESTS.json` reports 16 passing bounded
protocol controls; `evidence/COMBINED_INFRASTRUCTURE_TESTS.json` reports 11
passing source-reconstruction controls. Both test-script hashes were freshly
compared with those receipts and agree. These tests use synthetic or transformed
predecessor fixtures. They demonstrate rejection and reconstruction behavior;
they do not establish an Exp014 mathematical theorem or a current remote run.

During review, the primary agent cleared an inherited `LEAN_SYSROOT` from the
final verifier's environment and reran the 11 combined infrastructure controls
successfully. `evidence/ENVIRONMENT_ISOLATION_TEST.json` additionally records
five passing checks from the saved, reproducible
`test_environment_isolation.py`. They execute the actual
environment-construction AST against conflicting inherited Lean variables and
check the replaced project path, pinned core path, removed source/sysroot
overrides, preserved unrelated environment, and single-thread setting. The
receipt dated `2026-09-09T00:59:58.883601+00:00` binds the current checker and
test-script hashes. This reviewer inspected the saved test source, changed
checker lines, and receipt without rerunning them.

The initial environment record shows no preexisting project paths at
`/content/exp014_check`, with boot ID
`e287ac86-e5ac-4c47-ba61-dc22f05b8e83`. The local allocation record identifies
VM `m-s-kkb-use4c0-3g3ru54zvgn9o`, distinct from its recorded predecessor list.
These records were inspected, but this reviewer did not independently query
the Colab service. The receiving checker binds the exact saved environment
bytes, validates the allocation and boot identities, and later requires a
completed bootstrap and consistent chronology within the remote VM.

## Source reconstruction and import isolation

`make_combined.py` checks the fixed hashes of all three original Exp013 generic
sources and reconstructs `Exp013GenericFoundation.lean` exactly. It embeds
those bodies followed by the nine Exp014 modules, rejects unrecognized project
imports, and records each original/derived module hash. Its public theorem
catalog ignores comments and private declarations, tracks namespaces, and
rejects duplicate names. Its scanner is designed for the declaration forms
used in these sources; it is not a complete Lean parser.

`verify_combined.py` rebuilds the complete source and receipt and requires exact
equality before invoking Lean. It checks the fixed compiler binary hash,
dependency lock, helper hashes, pinned package commits and clean tracked
package sources. Its copied external dependency closure is placed in a fresh
output directory. The final `LEAN_PATH` contains that closure and the selected
compiler's core library. Project build outputs are excluded from that path,
and the combined file imports only external modules. The dependency walker
may leave compiler-core imports unresolved; the final Lean invocation must
still resolve every import and exit successfully.
Inherited `LEAN_SRC_PATH` and `LEAN_SYSROOT` are explicitly removed.

The verifier rejects placeholder/unsafe proof tokens, derives the accepted
axiom catalog from actual compiler output, requires exact expected-name
coverage, and allows only `propext`, `Classical.choice`, and `Quot.sound`.
After elaboration it rechecks combined/component source hashes, copied
artifact hashes, and dependency checkout state. The construction does not
claim to rebuild Lean or prove correspondence between dependency source and
downloaded compiled artifacts. Those compiler/library artifacts remain trusted
inputs, with cross-environment comparison of the external closure.

## Delivery, bootstrap, and receiving checks

The preparation scripts reconstruct the exact final source before packing it,
create explicit file-hash manifests, verify complete archive readback, and
refuse an already prepared delivery. Bootstrap inputs include the exact
combined source so that dependency cache requests are tied to its imports.
The bootstrap launcher was populated with the archive and driver hashes during
preparation. Its final substitutions have now been inspected and compared with
`BOOTSTRAP_INPUTS.json`; no launcher logic changed. The prepared launcher hash
is `a31fc5905109ebda7bfed760f4eb3697d7492f2e4175b89e2a4b9f6e7bc54a9e`.
The bootstrap archive hash is
`282703ece0a48347fdedf7400fde536be5fbf33961b621a3b188fa4b5264bec0`;
the bootstrap driver hash remains
`ac2578a873853e8058b0dae0be653fa4202244628faa0a27975994b5ff6de1c9`.
The final source archive hash is
`82984ac339762e4396d4e8ca96030c358401fe97bf9d948d93e705384f42534a`.
Independent readback in this review verified all six bootstrap members and all
21 final-source members against their manifests and current local bytes. Both
deliveries contain the exact combined source with SHA-256
`40d4c5fabfe49ad117ed5b442dd1e10f42a1fbf23afcc7b42a80ba9f5adb5aee`.

Both launchers verify delivery hashes and manifest coverage before writing
source/input files to new directories. They reject duplicate, unsafe, or
nonregular archive members. The bootstrap downloads the pinned compiler,
checks every dependency revision, builds the cache client, and downloads
compatible external artifacts. It clears inherited Lean path/sysroot
variables. Every external command has a recorded argument vector, return
code, elapsed time, and hashed log. The final launcher requires a passing
bootstrap for the exact combined source before starting verification.

The exporter requires a successful final remote result and includes sources,
inputs, controllers, command logs, and artifact manifests without build caches.
The receiver verifies archive/file hashes, safe member coverage, byte-for-byte
local/remote verification-input equality, launch pins, compiler/source pins,
fresh-bootstrap chronology, command vectors and logs, cache roots, axiom logs,
and equal local/remote external artifact manifests. Only after acceptance does
it extract into a new directory and publish a receipt binding both local and
received evidence bytes. The exporter's success flag is not sufficient by
itself; receiving validation and final seal gates remain necessary.

## Final acceptance and preservation

`finalize.py` requires accepted local, independent, and transfer results and
rechecks every accepted evidence hash. It binds the export archive to its
receipt, reconstructs the final source/catalog, and requires a review receipt
covering current sources, public-name count, review text, reviewed tools
(including the finalizer), and required explanatory documents. Every modular
source also needs a successful matching receipt, unchanged log, and matching
current compiled output. Predecessor manifests and preserved packet hashes
are checked before packaging.

The finalizer refuses an existing packet or sealed manifest. It creates an
explicit payload manifest, checks ZIP coverage, CRC and exact member readback,
rechecks payload/source bytes, and publishes the final external receipt only
after those checks. Its external receipt and neighboring checksum avoid a
self-hash cycle. Failed or interrupted runs do not qualify an experiment;
recovery snapshots remain separate from proof evidence.

## Final frozen review qualification

The table below includes the actual prepared launcher hash. All other reviewed
tool hashes remain unchanged from the preceding review. The final source
review covers all nine accepted modular files and the complete 143-name public
audit catalog, with 121 production statements and 22 controls. The local
combined check has subsequently passed all 143 audits. This source/tool review
does not claim that the pending independent proof check or its receiving
validation has passed.

The completion report's template correctly says: "The construction uses all
integer Fourier modes without a finite cutoff." Persistence of infinite
coefficient support for every trajectory is not established by the controls.

The environment-isolation improvement and mode-wording clarification raised
during this review have both been addressed; no unresolved blocker remains.

## Reviewed tool hashes

| File | SHA-256 |
|---|---|
| `make_combined.py` | `b32fced589091805cf3f1856862e4e50e1f025d595e474ad266dd145c75ed725` |
| `verify_combined.py` | `1fa19aff12c7b10833e3fac39224844d59a4802273b726a5fbbd783ec5e74554` |
| `prepare_final_sources.py` | `4250fcca196d3d67719aa3225f1589c5d6335c580cc74014a7674e0ea225341e` |
| `prepare_bootstrap_inputs.py` | `572dfd505cda8048c9637eaec1ad0ca4b803411ad52e7c61ce6356283d34b5f0` |
| `remote_check/bootstrap.py` | `ac2578a873853e8058b0dae0be653fa4202244628faa0a27975994b5ff6de1c9` |
| `remote_check/initialize.py` | `ee352b4053288d8de096a322bc192fceb1a6df7f4512bd39ab743bc922891c82` |
| `remote_check/start_bootstrap.py` | `a31fc5905109ebda7bfed760f4eb3697d7492f2e4175b89e2a4b9f6e7bc54a9e` |
| `remote_check/start_final.py` | `4e14f05d4bbde6786dd1aac6bbf4055e4cef20bb2bcaa4f83a52d0b2547771a6` |
| `remote_check/export_evidence.py` | `05c4e778f888846fbd1e9e81f04c62604abd3301462cfb539915f1fb946ddc4a` |
| `remote_check/check_download.py` | `26a6382e59c1fa7909a9d478cfe71448dd2b14363bd804666ad6575a72ef8992` |
| `finalize.py` | `2cc9ed30f2bcc05a924d37d1959bb6deb955d94716d7375258b7f83c6831e5cc` |
| `check_predecessors.py` | `3af57f3733c4c7a4e85dacaf73dfe2216d63ae9ead5410714026b68864c64bc2` |
| `test_infrastructure.py` | `ef604ebbbec39c1ab822a03756189d3f582a2bc179091e0ecd5e99a765c9459a` |
| `test_combined_infrastructure.py` | `1b60d36856c99ae8dfbbba0c1d45a7a76df2484f9cc77a72fe5a308fda668975` |
| `test_environment_isolation.py` | `20b08e469b746a48a7c81ba91551e23991d2a6a0b7d963313ed6715f161d4231` |

The pinned axiom-policy helper hash is
`fb33175f0ae151e50a1887d5093dac7010beaf990e936f0fd813e7b6e425fffb`,
and the pinned dependency-walker hash is
`12d648a6fca9b35c69d400d4695a97b5957fe50cb0a96038ef813ad6fba58057`.
