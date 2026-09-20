from __future__ import annotations

import logging
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Protocol

import matplotlib.pyplot as plt

log = logging.getLogger(__name__)

DEFAULT_DPI = 300


class OutputFormat(Enum):
    SVG = "svg"
    PNG = "png"
    PDF = "pdf"


def resolve_output_format(name: str) -> OutputFormat:
    for candidate in OutputFormat:
        if candidate.value == name.lower():
            return candidate
        else:
            continue
    known = ", ".join(item.value for item in OutputFormat)
    raise ValueError(f"unknown format {name!r}, available: {known}")


class FigureSink(Protocol):
    def path_for(self, name: str) -> Path:
        ...

    def write(self, figure: plt.Figure, name: str) -> Path:
        ...


@dataclass(frozen=True)
class FigureWriter:
    directory: Path
    output_format: OutputFormat = OutputFormat.SVG
    dpi: int = DEFAULT_DPI

    def path_for(self, name: str) -> Path:
        return self.directory / f"{name}.{self.output_format.value}"

    def prepare(self) -> None:
        self.directory.mkdir(parents=True, exist_ok=True)

    def write(self, figure: plt.Figure, name: str) -> Path:
        log.debug("writing figure %s", name)
        path = self.path_for(name)
        figure.tight_layout()
        figure.savefig(path, format=self.output_format.value, dpi=self.dpi)
        plt.close(figure)
        log.info("saved %s", path)
        return path
