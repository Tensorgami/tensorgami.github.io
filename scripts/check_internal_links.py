#!/usr/bin/env python3
"""Check local href/src targets in the static Tensorgami site."""

from __future__ import annotations

from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlparse


ROOT = Path(__file__).resolve().parents[1]
SKIP_DIRS = {".git", ".github"}
HTML_SUFFIXES = {".html", ".htm"}


class LinkParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.links: list[tuple[str, str]] = []
        self.anchors: set[str] = set()

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        for key, value in attrs:
            if value is None:
                continue
            if key in {"href", "src"}:
                self.links.append((key, value))
            elif key in {"id", "name"}:
                self.anchors.add(value)


def site_files() -> list[Path]:
    files: list[Path] = []
    for path in ROOT.rglob("*"):
        if any(part in SKIP_DIRS for part in path.parts):
            continue
        if path.is_file() and path.suffix.lower() in HTML_SUFFIXES:
            files.append(path)
    return sorted(files)


def parse_html(path: Path) -> LinkParser:
    parser = LinkParser()
    parser.feed(path.read_text(encoding="utf-8"))
    return parser


def internal_target(source: Path, raw_url: str) -> tuple[Path | None, str]:
    parsed = urlparse(raw_url)
    if parsed.scheme in {"http", "https", "mailto", "tel", "data", "javascript"}:
        return None, ""
    if parsed.netloc:
        return None, ""

    path = unquote(parsed.path)
    if not path:
        return source, parsed.fragment
    if path.startswith("/"):
        target = ROOT / path.lstrip("/")
    else:
        target = source.parent / path
    return target.resolve(), parsed.fragment


def display(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def html_for_fragment(target: Path) -> Path | None:
    if target.is_dir():
        index = target / "index.html"
        return index if index.exists() else None
    if target.suffix.lower() in HTML_SUFFIXES and target.exists():
        return target
    return None


def main() -> int:
    html_files = site_files()
    parsed_by_file = {path: parse_html(path) for path in html_files}
    failures: list[str] = []

    for source, parser in parsed_by_file.items():
        for attr, raw_url in parser.links:
            target, fragment = internal_target(source, raw_url)
            if target is None:
                continue
            if not target.exists():
                failures.append(f"{display(source)}: missing {attr} target {raw_url}")
                continue
            if fragment:
                fragment_file = html_for_fragment(target)
                if fragment_file is None:
                    continue
                anchors = parsed_by_file.get(fragment_file)
                if anchors is None:
                    anchors = parse_html(fragment_file)
                    parsed_by_file[fragment_file] = anchors
                if fragment not in anchors.anchors:
                    failures.append(
                        f"{display(source)}: missing fragment #{fragment} in "
                        f"{display(fragment_file)}"
                    )

    if failures:
        print("Internal link check failed:")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print(f"Checked {len(html_files)} HTML files; no missing internal links.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
