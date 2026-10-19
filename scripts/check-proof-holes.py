#!/usr/bin/env python3
"""Reject explicit proof holes and custom axioms outside the statement surface.

This deliberately conservative source check complements, and never replaces,
the comparator's transitive axiom audit. Challenge theorem holes are expected.
"""

import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def without_comments_and_strings(source: str) -> str:
    result = []
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        pair = source[index:index + 2]
        char = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            if char == "\\" and index + 1 < len(source):
                result.extend("\n" if c == "\n" else " " for c in source[index:index + 2])
                index += 2
            else:
                in_string = char != '"'
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end == -1:
                end = len(source)
            result.extend(" " * (end - index))
            index = end
        elif char == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(char)
            index += 1
    return "".join(result)


def main() -> int:
    failures = []
    for directory, directories, files in os.walk(ROOT, followlinks=False):
        directories[:] = sorted(name for name in directories if name not in {".git", ".lake"})
        for name in sorted(files):
            path = Path(directory) / name
            if path.suffix != ".lean" or path == ROOT / "Challenge.lean":
                continue
            source = without_comments_and_strings(path.read_text(encoding="utf-8"))
            for found in re.finditer(r"\b(sorry|admit|axiom)\b", source):
                line = source.count("\n", 0, found.start()) + 1
                failures.append(f"{path.relative_to(ROOT)}:{line}: forbidden {found.group()}")
    if failures:
        print("\n".join(failures))
        return 1
    print("No explicit proof holes or custom axioms outside Challenge.lean.")
    print("This does not establish the presence or completion of any main theorem.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
