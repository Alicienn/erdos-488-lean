#!/usr/bin/env python3
"""Check Palomar Lean source rules: UTF-8, `module` header, <= 10,000 lines, no symlinks."""
from __future__ import annotations

import os
import re
from pathlib import Path

WHITESPACE_OR_LINE_COMMENT = re.compile(r"(?:\s|--[^\n]*(?:\n|\Z))+")
COMMENT_MARKER = re.compile(r"/-|-/")
IDENTIFIER_CONTINUATION = re.compile(r"[\w'!?.]", re.UNICODE)


def has_module_header(text: str) -> bool:
    index = 0
    if text.startswith("\ufeff"):
        index = 1
    while index < len(text):
        match = WHITESPACE_OR_LINE_COMMENT.match(text, index)
        if match is not None:
            index = match.end()
            continue
        if text.startswith("/-", index) and not text.startswith("/-!", index):
            index += 2
            depth = 1
            while depth:
                marker = COMMENT_MARKER.search(text, index)
                if marker is None:
                    return False
                depth += 1 if marker.group() == "/-" else -1
                index = marker.end()
        else:
            return text.startswith("module", index) and (
                IDENTIFIER_CONTINUATION.match(text, index + 6) is None
            )
    return False


def physical_lines(text: str) -> int:
    return text.count("\n") + int(bool(text) and not text.endswith("\n"))


def lean_source_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for directory, subdirectories, names in os.walk(root, followlinks=False):
        subdirectories[:] = sorted(
            name
            for name in subdirectories
            if name not in {".git", ".lake"} and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            path = Path(directory) / name
            if name.endswith(".lean") and (path.is_symlink() or path.is_file()):
                files.append(path)
    return files


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failed = False
    for path in lean_source_files(root):
        relative = path.relative_to(root)
        if path.is_symlink():
            print(f"{relative}: must be a regular Lean file, not a symbolic link")
            failed = True
            continue
        try:
            text = path.read_bytes().decode("utf-8")
        except UnicodeDecodeError:
            print(f"{relative}: source is not valid UTF-8")
            failed = True
            continue
        if path.name != "lakefile.lean" and not has_module_header(text):
            print(f"{relative}: must use the module header keyword")
            failed = True
        if physical_lines(text) > 10_000:
            print(f"{relative}: exceeds 10,000 lines; split into smaller modules")
            failed = True
    if not failed:
        print("All Lean source files satisfy Palomar module and line-cap requirements.")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
