from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import matplotlib.pyplot as plt
import numpy as np

from .palette import Palette
from .schematics import SchematicCanvas

DEFAULT_WIDE_SIZE = (10.0, 4.6)
DEFAULT_DIAGRAM_SIZE = (10.0, 5.0)


@dataclass(frozen=True)
class GridSpecification:
    rows: int = 1
    columns: int = 1
    width_ratios: tuple[float, ...] | None = None
    shared_axis: str = "none"

    def keyword_arguments(self) -> dict[str, Any]:
        arguments: dict[str, Any] = {}
        if self.width_ratios is not None:
            arguments["gridspec_kw"] = {"width_ratios": list(self.width_ratios)}
        else:
            pass
        match self.shared_axis:
            case "none":
                pass
            case "x" | "y" | "all":
                arguments["sharex"] = self.shared_axis in ("x", "all")
                arguments["sharey"] = self.shared_axis in ("y", "all")
            case other:
                raise ValueError(f"unknown shared axis {other!r}")
        return arguments


@dataclass(frozen=True)
class FigureContext:
    palette: Palette
    random: np.random.Generator
    seed: int = 0

    def spawn_random(self, offset: int) -> np.random.Generator:
        return np.random.default_rng(self.seed + offset)

    def blank_canvas(
        self, size: tuple[float, float] = DEFAULT_DIAGRAM_SIZE
    ) -> SchematicCanvas:
        return SchematicCanvas(self.palette, size)

    def create_figure(
        self,
        size: tuple[float, float] = DEFAULT_WIDE_SIZE,
        grid: GridSpecification = GridSpecification(),
    ) -> tuple[plt.Figure, Any]:
        return plt.subplots(
            grid.rows, grid.columns, figsize=size, **grid.keyword_arguments()
        )
