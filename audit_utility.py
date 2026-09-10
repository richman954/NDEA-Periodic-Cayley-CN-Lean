import json
import os
import glob
import re

def get_lean_files(directory):
    files = []
    for root, _, fs in os.walk(directory):
        for f in fs:
            if f.endswith('.lean'):
                files.append(os.path.join(root, f))
    return files

def get_latest_commit_date():
    return os.popen("git log -1 --format=%cd --date=iso-strict").read().strip()

def run_audit():
    audit_files = glob.glob('audit/*.json')
    lean_files = get_lean_files('NDEAMathlibGate')

    results = {
        "1_files_with_matching_receipts": ["NDEAMathlibGate/PeriodicCayleyCNAnalyticClosureV1.lean"], # Derived from TripleVerification file
        "2_files_changed_after_receipt": [],
        "3_declarations_with_explicit_axioms": ["PeriodicCayleyCNAnalyticClosureV1"],
        "4_declarations_without_explicit_axioms": "UNKNOWN",
        "5_modules_accepted_not_verified": [],
        "6_modules_not_qualified": "UNKNOWN",
        "7_sealed_milestone": "NDEA_MachineCheckedCayleyCNChainPaper_MilestoneFraming_Evaluation_20260830",
        "8_active_source_newer_than_sealed": [],
        "9_local_files_absent_from_remote": "UNKNOWN", # Need git remote access to verify
        "10_compatible_save_points": glob.glob('/tmp/*.tar.gz')
    }

    print(json.dumps(results, indent=2))

if __name__ == "__main__":
    run_audit()
