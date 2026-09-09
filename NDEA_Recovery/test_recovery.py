#!/usr/bin/env python3
"""One real capture/restore exercise plus corruption and traversal controls."""
import json
import contextlib
import io
from pathlib import Path
import signal
import tempfile
import zipfile

import checkpoint


def rejected(action):
    try:
        action()
    except (ValueError, zipfile.BadZipFile):
        return True
    raise AssertionError("Invalid recovery input was accepted")


def check_task_selection():
    original = checkpoint.HERE, checkpoint.PROJECT, checkpoint.WORKSPACE
    signals = {s: signal.getsignal(s) for s in [signal.SIGTERM, signal.SIGINT]}
    with tempfile.TemporaryDirectory(prefix="task-selection-test-", dir=checkpoint.HERE) as temporary:
        try:
            checkpoint.WORKSPACE = Path(temporary)
            checkpoint.HERE = Path(temporary) / "recovery"
            checkpoint.PROJECT = Path(temporary) / "project"
            checkpoint.HERE.mkdir()
            checkpoint.PROJECT.mkdir()
            for name in ["RESUME_STATUS.md", "WORKING_ROADMAP.md"]:
                (checkpoint.PROJECT / name).write_text("Fixture recovery notes\n")
            selected = checkpoint.PROJECT / "exp013"
            selected.mkdir()
            (selected / "proof.lean").write_text("-- Recovery selection fixture, not proof evidence\n")
            previous = checkpoint.PROJECT / "exp012/evidence"
            previous.mkdir(parents=True)
            (previous / "FINAL_PACKET_RECEIPT.json").write_text('{"fixture": true}\n')
            state = checkpoint.HERE / "TASK_STATE.json"
            state.write_text(json.dumps({"active_experiment": str(selected)}))
            assert checkpoint.active_experiment(state) == selected
            first = checkpoint.snapshot_once(state, "selected_task_without_final_receipt")
            assert first["active_experiment"] == "exp013"
            assert first["final_packet_receipt_captured"] is False
            (selected / "evidence").mkdir()
            (selected / "evidence/FINAL_PACKET_RECEIPT.json").write_text('{"fixture": true}\n')
            with contextlib.redirect_stdout(io.StringIO()):
                checkpoint.watch(state, 60, 12)
            status = json.loads((checkpoint.HERE / "WATCHER_STATUS.json").read_text())
            final = json.loads((checkpoint.HERE / "LATEST_CHECKPOINT.json").read_text())
            assert status["status"] == "stopped"
            assert status["stop_reason"] == "final_packet_receipt_captured"
            assert final["active_experiment"] == "exp013"
            assert final["final_packet_receipt_captured"] is True
            state.write_text(json.dumps({"active_experiment": "/tmp"}))
            outside_rejected = rejected(lambda: checkpoint.active_experiment(state))
            (checkpoint.PROJECT / "exp014").symlink_to(selected, target_is_directory=True)
            state.write_text(json.dumps({"active_experiment": "exp014"}))
            symlink_rejected = rejected(lambda: checkpoint.active_experiment(state))
            return {"old_experiment_receipt_did_not_complete_selected_task": True,
                    "watcher_stopped_after_matching_task_receipt_captured": True,
                    "outside_project_selection_rejected": outside_rejected,
                    "symlink_experiment_selection_rejected": symlink_rejected}
        finally:
            checkpoint.HERE, checkpoint.PROJECT, checkpoint.WORKSPACE = original
            for sig, handler in signals.items():
                signal.signal(sig, handler)


def main():
    task_selection = check_task_selection()
    pointer = checkpoint.snapshot_once(reason="recovery_readback_test")
    archive = Path(pointer["archive"])
    digest = pointer["archive_sha256"]
    checked = checkpoint.verify_archive(archive, digest)
    assert checked["manifest"]["task_state_present"]
    assert "NDEA_Recovery/checkpoint.py" in checked["manifest"]["files"]
    assert "NDEA_Recovery/TASK_STATE.json" in checked["manifest"]["files"]
    with tempfile.TemporaryDirectory(prefix="recovery-test-", dir=checkpoint.HERE) as temporary:
        root = Path(temporary)
        restored = checkpoint.restore_archive(archive, digest, root / "restored")
        assert restored["files_verified"] == checked["payload_files_verified"]
        damaged = root / "damaged.zip"
        data = bytearray(archive.read_bytes())
        data[len(data) // 2] ^= 1
        damaged.write_bytes(data)
        outer_damage_rejected = rejected(lambda: checkpoint.verify_archive(damaged, digest))
        stale = root / "stale-payload.zip"
        with zipfile.ZipFile(archive) as source, zipfile.ZipFile(stale, "w") as output:
            first = True
            for info in source.infolist():
                data = source.read(info)
                if first and info.filename != checkpoint.MANIFEST:
                    data += b"changed payload"
                    first = False
                checkpoint.write_member(output, info.filename, data)
        payload_damage_rejected = rejected(
            lambda: checkpoint.verify_archive(stale, checkpoint.file_sha(stale)))
        unsafe = root / "unsafe.zip"
        with zipfile.ZipFile(archive) as source, zipfile.ZipFile(unsafe, "w") as output:
            for info in source.infolist():
                checkpoint.write_member(output, info.filename, source.read(info))
            # Deliberately bypass the safe writer to exercise hostile archive input.
            output.writestr("../escape.txt", b"must never be restored")
        unsafe_target = root / "unsafe-restore"
        unsafe_rejected = rejected(lambda: checkpoint.restore_archive(
            unsafe, checkpoint.file_sha(unsafe), unsafe_target))
        assert not unsafe_target.exists() and not (root / "escape.txt").exists()
        pointer_readback = json.loads((checkpoint.HERE / "LATEST_CHECKPOINT.json").read_text())
        assert pointer_readback == pointer
        assert checkpoint.file_sha(Path(pointer["receipt"])) == pointer["receipt_sha256"]
    report = {
        "passed": True, "completed_utc": checkpoint.utc(),
        "utility_sha256": checkpoint.file_sha(checkpoint.HERE / "checkpoint.py"),
        "test_sha256": checkpoint.file_sha(Path(__file__).resolve()),
        "archive": str(archive), "archive_sha256": digest,
        "payload_files_verified_and_restored": checked["payload_files_verified"],
        "published_pointer_and_receipt_verified": True,
        "outer_hash_damage_rejected": outer_damage_rejected,
        "payload_hash_damage_rejected": payload_damage_rejected,
        "unsafe_path_rejected_before_restore": unsafe_rejected,
        "task_selection": task_selection,
        "temporary_restore_removed_after_verification": True,
        "proof_completion_evidence": False,
        "scope": "Actual recovery archive readback and restored file hashes, with focused corruption/path controls; no Lean rerun or power-loss simulation.",
    }
    checkpoint.atomic_bytes(checkpoint.HERE / "RECOVERY_TEST_RESULT.json", checkpoint.json_bytes(report))
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
