from __future__ import annotations

import os
import re
import sys
import unicodedata
from dataclasses import dataclass
from pathlib import Path

import pymupdf

MINIMUM_WORD_LENGTH = 4
EDGE_MARGIN_POINTS = 8.0
FRONT_MATTER_LINES = 10
REPOSITORY_DIR = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class SlideReport:
    number: int
    missing: tuple[str, ...] = ()
    crowded: tuple[str, ...] = ()

    def describe(self) -> str:
        parts = []
        if self.missing:
            parts.append("nedostaje: " + ", ".join(sorted(set(self.missing))))
        if self.crowded:
            parts.append("uz ivicu: " + " / ".join(self.crowded))
        return "; ".join(parts)


def is_marp_source(path: Path) -> bool:
    with path.open() as handle:
        head = [next(handle, "") for _ in range(FRONT_MATTER_LINES)]
    return any(line.startswith("marp: true") for line in head)


def discover_decks() -> list[tuple[Path, Path]]:
    distribution = os.environ.get("DIST_PDF", "")
    decks = []
    for markdown in sorted(REPOSITORY_DIR.glob("*/*.md")):
        if not is_marp_source(markdown):
            continue
        candidates = [markdown.with_suffix(".pdf")]
        if distribution:
            candidates.insert(0, Path(distribution) / f"{markdown.stem}.pdf")
        for candidate in candidates:
            if candidate.exists():
                decks.append((markdown, candidate))
                break
    return decks


def normalized(text: str) -> str:
    folded = unicodedata.normalize("NFKC", text)
    return " ".join(folded.split())


SEPARATOR_PATTERN = re.compile(r"(?m)^---[ \t]*$")


def slide_sources(markdown: Path) -> list[str]:
    text = markdown.read_text()
    parts = SEPARATOR_PATTERN.split(text)
    return parts[2:] if text.lstrip().startswith("---") else parts


def prose_words(markdown: str) -> list[str]:
    body = unicodedata.normalize("NFKC", markdown)
    body = re.sub(r"\$\$.*?\$\$", " ", body, flags=re.S)
    body = re.sub(r"\$[^$\n]*\$", " ", body)
    body = re.sub(r"```.*?```", " ", body, flags=re.S)
    body = re.sub(r"!\[[^\]]*\]\([^)]*\)", " ", body)
    body = re.sub(r"<!--.*?-->", " ", body, flags=re.S)
    body = re.sub(r"[#*`|>_\\]", " ", body)
    pattern = rf"[A-Za-zČĆŠŽĐčćšžđ]{{{MINIMUM_WORD_LENGTH},}}"
    return re.findall(pattern, body)


def crowded_blocks(page: pymupdf.Page) -> tuple[str, ...]:
    limit = page.rect.height - EDGE_MARGIN_POINTS
    return tuple(
        normalized(block[4])[:40]
        for block in page.get_text("blocks")
        if block[3] > limit and normalized(block[4])
    )


def check_whole_deck(markdown: Path, pdf: Path) -> list[SlideReport]:
    document = pymupdf.open(pdf)
    rendered = normalized(
        " ".join(
            document[index].get_text()
            for index in range(document.page_count)
        )
    )
    source = "\n".join(slide_sources(markdown))
    missing = tuple(
        word for word in prose_words(source)
        if normalized(word) not in rendered
    )
    return [SlideReport(0, missing)] if missing else []


def check_deck(markdown: Path, pdf: Path) -> list[SlideReport]:
    document = pymupdf.open(pdf)
    sources = slide_sources(markdown)
    if len(sources) != document.page_count:
        return check_whole_deck(markdown, pdf)
    reports = []
    for index, source in enumerate(sources):
        if index >= document.page_count:
            reports.append(SlideReport(index + 1, ("<nema strane>",)))
        else:
            page = document[index]
            rendered = normalized(page.get_text())
            missing = tuple(
                word for word in prose_words(source)
                if normalized(word) not in rendered
            )
            crowded = crowded_blocks(page)
            if missing or crowded:
                reports.append(SlideReport(index + 1, missing, crowded))
    return reports


def main() -> int:
    failures = 0
    warnings = 0
    decks = discover_decks()
    if not decks:
        print("nema izgrađenih prezentacija")
        return 1
    for markdown, pdf in decks:
        reports = check_deck(markdown, pdf)
        missing = [report for report in reports if report.missing]
        crowded = [report for report in reports if not report.missing]
        print(f"{pdf}: {len(missing)} sa nedostajućim tekstom, "
              f"{len(crowded)} uz ivicu")
        for report in reports:
            print(f"  slajd {report.number}: {report.describe()}")
        failures += len(missing)
        warnings += len(crowded)
    if warnings:
        print(f"upozorenja: {warnings}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
