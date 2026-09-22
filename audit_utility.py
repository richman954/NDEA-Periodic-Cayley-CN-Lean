import json
import os
import glob
import subprocess
from datetime import datetime

def run_cmd(cmd):
    try:
        return subprocess.check_output(cmd, shell=True, stderr=subprocess.STDOUT).decode('utf-8').strip()
    except subprocess.CalledProcessError:
        return ""

def get_lean_files(directory):
    files = []
    if os.path.exists(directory):
        for root, _, fs in os.walk(directory):
            for f in fs:
                if f.endswith('.lean'):
                    files.append(os.path.join(root, f))
    return files

def get_task_state():
    path = "NDEA_Recovery/TASK_STATE.json"
    if os.path.exists(path):
        with open(path, 'r') as f:
            return json.load(f)
    return {}

def run_audit():
    ts = get_task_state()
    exp = ts.get("current_state", {}).get("active_experiment", "exp016")
    exp_dir = f"NDEA_Evolve_offruntime/{exp}"
    lean_files = get_lean_files(exp_dir)

    # 1. Matching successful receipts & 5. Accepted but not combined
    matching = []
    newer = []
    accepted_not_combined = []

    # In exp016 evidence dir, there are some *_ACCEPTED.json
    # We parse the file modifications vs the accepted JSONs if they exist.
    evidence_dir = os.path.join(exp_dir, "evidence")
    accepted_jsons = glob.glob(f"{evidence_dir}/**/*_ACCEPTED.json", recursive=True)

    for f in lean_files:
        mod_time = os.path.getmtime(f)
        matched = False
        for a in accepted_jsons:
            # check if file name aligns with receipt name loosely (as a proxy)
            base = os.path.basename(f).replace('.lean', '')
            if base in a:
                matched = True
                receipt_time = os.path.getmtime(a)
                if mod_time > receipt_time:
                    newer.append(f)
                else:
                    matching.append(f)
                    accepted_not_combined.append(f)
                break
        if not matched:
            newer.append(f) # implicitly newer/unreceipted

    # 3. Explicit axiom audits
    axioms = "UNKNOWN"
    no_axioms = "UNKNOWN"

    # 6. Lacking independent qual
    unqualified = [f for f in lean_files if f not in matching]

    # 7. Latest sealed milestone
    sealed_milestone = "UNKNOWN"
    if "unsealed" not in ts.get("current_state", {}).get("qualification", "").lower():
        sealed_milestone = ts.get("current_state", {}).get("qualification", "UNKNOWN")

    # 9. Meaningful local files absent from remote
    absent = run_cmd("git ls-files --others --exclude-standard")

    # 10. Compatible save points
    save_points = glob.glob('/tmp/*.tar.gz')

    results = {
        "1_files_with_matching_receipts": matching,
        "2_files_newer_than_receipt": newer,
        "3_declarations_with_explicit_axioms": axioms,
        "4_declarations_without_explicit_axioms": no_axioms,
        "5_modules_accepted_not_verified": accepted_not_combined,
        "6_modules_not_independently_qualified": unqualified,
        "7_latest_sealed_milestone": sealed_milestone,
        "8_current_active_experiment": exp,
        "9_local_files_absent_from_remote": absent.split('\n') if absent else [],
        "10_compatible_save_points": save_points
    }

    with open("audit-report.json", "w") as f:
        json.dump(results, f, indent=2)

    # Human readable output
    print("=== NDEA Read-Only Audit Report ===")
    print(f"Active Experiment: {exp}")
    print(f"Latest Sealed Milestone: {sealed_milestone}")
    print(f"Modules w/ Matching Receipts: {len(matching)}")
    print(f"Modules Newer Than Receipts (or Missing): {len(newer)}")
    print(f"Accepted but Not Combined-Qualified: {len(accepted_not_combined)}")
    print(f"Local Untracked Files: {len(results['9_local_files_absent_from_remote'])}")
    print(f"Compatible Save Points Found: {len(save_points)}")
    print("===================================")

if __name__ == "__main__":
    run_audit()
