import unittest
import os
import json
import time

class TestAuditUtility(unittest.TestCase):
    def setUp(self):
        # Create a mock environment
        os.makedirs("test_env/NDEA_Evolve_offruntime/exp999/lean", exist_ok=True)
        os.makedirs("test_env/NDEA_Evolve_offruntime/exp999/evidence", exist_ok=True)
        os.makedirs("test_env/NDEA_Recovery", exist_ok=True)

        with open("test_env/NDEA_Recovery/TASK_STATE.json", "w") as f:
            json.dump({"current_state": {"active_experiment": "exp999", "qualification": "unsealed milestone"}}, f)

        # 1. Matching receipt file
        with open("test_env/NDEA_Evolve_offruntime/exp999/lean/MatchingModule.lean", "w") as f:
            f.write("def x := 1")
        time.sleep(0.1)
        with open("test_env/NDEA_Evolve_offruntime/exp999/evidence/MatchingModule_ACCEPTED.json", "w") as f:
            f.write("{}")

        # 2. Stale receipt file (module is newer)
        with open("test_env/NDEA_Evolve_offruntime/exp999/evidence/StaleModule_ACCEPTED.json", "w") as f:
            f.write("{}")
        time.sleep(0.1)
        with open("test_env/NDEA_Evolve_offruntime/exp999/lean/StaleModule.lean", "w") as f:
            f.write("def y := 2")

        # 3. Missing receipt -> UNKNOWN
        with open("test_env/NDEA_Evolve_offruntime/exp999/lean/MissingModule.lean", "w") as f:
            f.write("def z := 3")

    def test_audit(self):
        import audit_utility

        original_get_task_state = audit_utility.get_task_state
        original_get_lean_files = audit_utility.get_lean_files
        original_glob = audit_utility.glob.glob

        def get_task_state_mock():
            with open("test_env/NDEA_Recovery/TASK_STATE.json", "r") as f:
                return json.load(f)

        def get_lean_files_mock(directory):
            return original_get_lean_files(directory.replace("NDEA_Evolve_offruntime", "test_env/NDEA_Evolve_offruntime"))

        def glob_mock(pattern, recursive=False):
            if "NDEA_Evolve_offruntime" in pattern:
                pattern = pattern.replace("NDEA_Evolve_offruntime", "test_env/NDEA_Evolve_offruntime")
            return original_glob(pattern, recursive=recursive)

        audit_utility.get_task_state = get_task_state_mock
        audit_utility.get_lean_files = get_lean_files_mock
        audit_utility.glob.glob = glob_mock

        audit_utility.run_audit()

        audit_utility.get_task_state = original_get_task_state
        audit_utility.get_lean_files = original_get_lean_files
        audit_utility.glob.glob = original_glob

        with open("audit-report.json", "r") as f:
            res = json.load(f)

        self.assertEqual(res["8_current_active_experiment"], "exp999")
        self.assertTrue(any("MatchingModule.lean" in x for x in res["1_files_with_matching_receipts"]))
        self.assertTrue(any("StaleModule.lean" in x for x in res["2_files_newer_than_receipt"]))
        self.assertTrue(any("MissingModule.lean" in x for x in res["2_files_newer_than_receipt"]))
        self.assertEqual(res["7_latest_sealed_milestone"], "UNKNOWN")

    def tearDown(self):
        os.system("rm -rf test_env")

if __name__ == "__main__":
    unittest.main()
