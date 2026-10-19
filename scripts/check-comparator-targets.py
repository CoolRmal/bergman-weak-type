#!/usr/bin/env python3
"""Reject a comparator configuration that silently drops a planned main result.

This checks the comparison surface, not its proofs. The actual comparator must
still build, export, compare, and independently check every selected theorem.
"""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REQUIRED = {
    "BergmanWeakType.projection_constant_eq_one",
    "BergmanWeakType.positiveProjection_constant_eq_one",
    "BergmanWeakType.weightedPositiveProjection_constant_eq",
    "BergmanWeakType.one_le_weightedProjection_constant",
    "BergmanWeakType.weightedProjection_constant_le",
    "BergmanWeakType.boundaryConstant_le_weightedProjection_constant",
    "BergmanWeakType.positive_constant_eq_one_iff_disk",
}
PERMITTED = {"propext", "Quot.sound", "Classical.choice"}


def main() -> None:
    path = ROOT / "comparator.json"
    try:
        config = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as error:
        raise SystemExit(f"Cannot read the comparison configuration: {error}")
    if not isinstance(config, dict):
        raise SystemExit("comparator.json must contain one JSON object")
    expected_keys = {
        "challenge_module", "solution_module", "theorem_names",
        "definition_names", "permitted_axioms", "enable_nanoda",
    }
    if set(config) - expected_keys:
        raise SystemExit(f"Unsupported configuration keys: {sorted(set(config) - expected_keys)}")
    if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
        raise SystemExit("The comparison must use the public Challenge and Solution modules")
    names = config.get("theorem_names")
    if not isinstance(names, list) or not all(isinstance(name, str) for name in names):
        raise SystemExit("theorem_names must be a list of declaration names")
    if len(names) != len(set(names)):
        raise SystemExit("theorem_names must not contain duplicates")
    missing = REQUIRED - set(names)
    if missing:
        raise SystemExit("Missing advertised comparison targets: " + ", ".join(sorted(missing)))
    axioms = config.get("permitted_axioms")
    if not isinstance(axioms, list) or not all(isinstance(name, str) for name in axioms):
        raise SystemExit("permitted_axioms must explicitly list permitted standard axioms")
    if set(axioms) - PERMITTED:
        raise SystemExit("Only propext, Quot.sound, and Classical.choice may be permitted")
    if config.get("definition_names", []) != []:
        raise SystemExit("The mathematical operators must be defined, not comparator definition holes")
    for module in ("Challenge", "Solution"):
        if not (ROOT / f"{module}.lean").is_file():
            raise SystemExit(f"Missing {module}.lean")
    print(f"The comparison selects all {len(REQUIRED)} planned main targets; proofs are not yet checked.")


if __name__ == "__main__":
    main()
