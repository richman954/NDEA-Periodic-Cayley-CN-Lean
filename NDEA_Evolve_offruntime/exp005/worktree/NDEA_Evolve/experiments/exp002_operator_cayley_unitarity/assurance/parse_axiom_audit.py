#!/usr/bin/env python3
"""Turn the preserved Lean print/check log into a strict audit result."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
LOG = HERE.parent / "logs" / "final_axiom_audit.log"
OUTPUT = HERE / "final_axiom_audit_results.json"

DECLARATIONS = (
    "NDEAEvolve.Exp002.cayleyD_isUnit",
    "NDEAEvolve.Exp002.cayleyD_det_ne_zero",
    "NDEAEvolve.Exp002.cayley_unitary",
    "NDEAEvolve.Exp002.cayley_preserves_inner",
    "NDEAEvolve.Exp002.cayley_preserves_norm",
    "NDEAEvolve.Exp002.orderedCayleyProduct_unitary",
    "NDEAEvolve.Exp002.orderedCayleyProduct_preserves_inner",
    "NDEAEvolve.Exp002.orderedCayleyProduct_preserves_norm",
    "NDEAEvolve.Exp002.cayley_order_defect",
    "NDEAEvolve.Exp002.cayley_commute_iff_of_inverse_laws",
    "NDEAEvolve.Exp002.hermitian_cayley_commute_iff",
    "NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_factors_order_sensitive",
    "NDEAEvolve.Exp002.AdversarialWitnesses.pauli_cayley_commutator_wrong_sign",
    "NDEAEvolve.Exp002.AdversarialWitnesses.nonhermitian_cayley_not_unitary",
    "NDEAEvolve.Exp002.AdversarialWitnesses.complex_step_half_not_unitary",
    "NDEAEvolve.Exp002.AdversarialWitnesses.zero_step_breaks_commutation_iff",
    "NDEAEvolve.Exp002.AdversarialWitnesses.cayleyR_one_sided_inverse_permutation_detected",
)

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_BLOCK = re.compile(
    r"^'([^'\n]+)' depends on axioms: \[([A-Za-z0-9_.,\s]*)\]$",
    re.MULTILINE,
)
NO_AXIOM_LINE = re.compile(
    r"^'([^'\n]+)' does not depend on any axioms$", re.MULTILINE
)
AXIOM_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*")


def fail(message: str) -> None:
    raise SystemExit(f"AXIOM_AUDIT_PARSE_STATUS=FAIL\nREASON={message}")


def is_signature_start(line: str, name: str) -> bool:
    return line.startswith(name + " :") or line.startswith("@" + name + " :")


def main() -> int:
    if len(sys.argv) > 2:
        fail("usage: parse_axiom_audit.py [LOG]")
    log_path = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else LOG
    if OUTPUT.exists():
        fail(f"refusing to overwrite existing result: {OUTPUT}")
    try:
        lines = log_path.read_text(encoding="utf-8", errors="strict").splitlines()
    except (OSError, UnicodeError) as error:
        fail(f"cannot read log: {error}")

    starts: list[tuple[int, str]] = []
    for index, line in enumerate(lines):
        for name in DECLARATIONS:
            if is_signature_start(line, name):
                starts.append((index, name))
                break
    if tuple(name for _, name in starts) != DECLARATIONS:
        fail(f"signature sequence mismatch: {[name for _, name in starts]!r}")

    signatures: dict[str, str] = {}
    first_print = next((i for i, line in enumerate(lines) if line.startswith("theorem ")), len(lines))
    for offset, (start, name) in enumerate(starts):
        stop = starts[offset + 1][0] if offset + 1 < len(starts) else first_print
        signature = "\n".join(lines[start:stop]).strip()
        if not signature or not is_signature_start(signature, name):
            fail(f"empty or malformed signature for {name}")
        signatures[name] = signature

    axiom_rows: dict[str, list[str]] = {}
    for match in AXIOM_BLOCK.finditer("\n".join(lines)):
        name, payload = match.groups()
        axioms = [] if not payload.strip() else [item.strip() for item in payload.split(",")]
        if any(AXIOM_NAME.fullmatch(axiom) is None for axiom in axioms):
            fail(f"malformed axiom name list for {name}: {axioms!r}")
        if name in axiom_rows:
            fail(f"duplicate axiom report for {name}")
        axiom_rows[name] = axioms
    for match in NO_AXIOM_LINE.finditer("\n".join(lines)):
        name = match.group(1)
        if name in axiom_rows:
            fail(f"duplicate axiom report for {name}")
        axiom_rows[name] = []

    if set(axiom_rows) != set(DECLARATIONS):
        fail(
            "axiom declaration mismatch: "
            f"missing={sorted(set(DECLARATIONS) - set(axiom_rows))!r} "
            f"extra={sorted(set(axiom_rows) - set(DECLARATIONS))!r}"
        )
    unexpected = sorted({axiom for values in axiom_rows.values() for axiom in values} - ALLOWED_AXIOMS)
    forbidden = sorted(
        axiom for values in axiom_rows.values() for axiom in values
        if "sorryAx" in axiom or "unsafe" in axiom or "native_decide" in axiom
    )
    result = {
        "schema": "ndea.exp002.axiom_audit.v1",
        "status": "PASS" if not unexpected and not forbidden else "FAIL",
        "source_log": str(log_path),
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "unexpected_axioms": unexpected,
        "forbidden_dependencies": forbidden,
        "declarations": [
            {"name": name, "signature": signatures[name], "axioms": axiom_rows[name]}
            for name in DECLARATIONS
        ],
    }
    with OUTPUT.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": result["status"],
        "declaration_count": len(DECLARATIONS),
        "unexpected_axioms": unexpected,
        "forbidden_dependencies": forbidden,
    }, indent=2, sort_keys=True))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
