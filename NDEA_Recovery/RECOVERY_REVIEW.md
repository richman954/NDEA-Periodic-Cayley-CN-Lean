# Independent recovery review — September 8, 2026

No blocking recovery issue remains in the reviewed utilities. This review
covered source selection, saved resume state, integrity checks, publication,
and restoration. It did not rerun Lean or modify sealed experiment files.

The checkpoint now selects the active `expNNN` directory from `TASK_STATE.json`.
The previous experiment's final receipt cannot stop a later experiment's
watcher. Its explicit metadata list includes the primary restart guide,
recovery policy, task/run state, utilities, this review, and available release
and off-machine backup records. Snapshot and release directories are excluded
from recursive capture. Completed predecessor packets are preserved separately
in the completed-release bundle.

I independently read the recovery-test archive and verified all 188 payload
hashes. All eight current Experiment 012 Lean files were present, alongside
the central notes, `START_HERE.md`, policy, task state and available release
records. The passing recovery-test receipt matches the current utility and
test source hashes. Its tests exercised a real restore, archive and payload
corruption, unsafe paths, active-task selection and completion-marker behavior.

The completed-release utility requires its listed releases, companion Git
bundles/receipts, embedded utility and inventory. It checks available original
checksums and accepted receipts, archive CRCs, exact archive readback, and
unchanged original bytes. The Experiment 005 packet includes its original
source archive and Git bundle. Both restoration utilities reject an existing
destination and symlinked destination ancestors. The release restorer stages
and verifies files before publishing the new destination.

Two review findings were corrected: incomplete required-companion checking
in release verification, and allowing symlinked restore ancestors. The final
release test receipt records eight passing checks, including a 40-file restore,
execution of the restored verifier, missing Git-bundle rejection with a
consistent manifest, corruption rejection and existing-destination protection.

Reviewed source and evidence pins:

| File | SHA-256 |
|---|---|
| `checkpoint.py` | `d5b77bbb618eb2cc5f03ed02fb9480a5321a260e2315e2178ba8196f1a1bcdb9` |
| `test_recovery.py` | `f8261422df3d481d4e9747cb5c057bed426b4f2495b326c565fa0671a1ed8d4f` |
| `archive_releases.py` | `6a1d2ea6cb031919ae19a1c8dcc9ceb92421364250a1b3e54f01bccaa6030987` |
| `RECOVERY_TEST_RESULT.json` | `4de4112ec1cc70d76b51e81d2960f4b992c08a7c5ed9f901d06c707757ab9d96` |
| `RELEASE_ARCHIVE_TEST_RESULT.json` | `8c5414c5a5e20caef93ff966fbfcf863b88bad44c147f5bdd8ece15a33595906` |

The final release bundle has SHA-256
`1f54a8205a6c26f354fff837de611ee910d148fd42e3e80b4722389360591f18`.

The remaining operational step is a final checkpoint after the review and
backup receipts are saved. Check the actual off-machine receipt before claiming
that copy exists. A Colab VM is temporary storage; permanent backup remains a
separate destination. After restoration, remap saved absolute paths to the new
workspace and restart any needed watcher. Sequential snapshots are recovery
copies, not transactional snapshots or new proof checks; no power-loss test
was performed.
