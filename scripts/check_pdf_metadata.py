#!/usr/bin/env python3
"""Check that public PDFs carry basic bibliographic metadata."""

from __future__ import annotations

from pathlib import Path

from pypdf import PdfReader


ROOT = Path(__file__).resolve().parents[1]
PDF_ROOT = ROOT / "pdfs"
REQUIRED_FIELDS = ["/Title", "/Author", "/Subject", "/Keywords"]
AUTHOR = "Henry Shin"


def display(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def clean(value: object) -> str:
    if value is None:
        return ""
    return str(value).strip()


def main() -> int:
    pdfs = sorted(PDF_ROOT.rglob("*.pdf"))
    failures: list[str] = []

    if not pdfs:
        failures.append("No PDFs found under pdfs/.")

    for pdf in pdfs:
        try:
            reader = PdfReader(str(pdf))
        except Exception as exc:
            failures.append(f"{display(pdf)}: could not read PDF metadata: {exc}")
            continue

        metadata = reader.metadata or {}
        for field in REQUIRED_FIELDS:
            if not clean(metadata.get(field)):
                failures.append(f"{display(pdf)}: missing {field}")

        author = clean(metadata.get("/Author"))
        if author != AUTHOR:
            failures.append(f"{display(pdf)}: /Author is {author!r}, expected {AUTHOR!r}")

    if failures:
        print("PDF metadata check failed:")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print(f"Checked {len(pdfs)} PDFs; required metadata is present.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
