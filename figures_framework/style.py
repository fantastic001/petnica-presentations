from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Protocol

import matplotlib.pyplot as plt

from .palette import LIGHT_PALETTE, Palette, resolve_palette


@dataclass(frozen=True)
class TypographyScale:
    body: float = 16.0
    title: float = 18.0
    legend: float = 15.0


class StyleProfile(Protocol):
    palette: Palette

    def apply(self) -> None:
        ...


@dataclass(frozen=True)
class MatplotlibStyleProfile:
    palette: Palette
    typography: TypographyScale = TypographyScale()
    line_width: float = 2.2
    grid_line_width: float = 0.8

    def parameters(self) -> dict[str, Any]:
        return {
            "figure.facecolor": self.palette.surface,
            "axes.facecolor": self.palette.surface,
            "savefig.facecolor": self.palette.surface,
            "axes.edgecolor": self.palette.muted_ink,
            "axes.labelcolor": self.palette.ink,
            "axes.titlecolor": self.palette.ink,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.grid": True,
            "axes.prop_cycle": plt.cycler(color=self.palette.series()),
            "grid.color": self.palette.grid,
            "grid.linewidth": self.grid_line_width,
            "xtick.color": self.palette.muted_ink,
            "ytick.color": self.palette.muted_ink,
            "text.color": self.palette.ink,
            "font.size": self.typography.body,
            "axes.titlesize": self.typography.title,
            "legend.fontsize": self.typography.legend,
            "legend.frameon": False,
            "lines.linewidth": self.line_width,
        }

    def apply(self) -> None:
        plt.rcParams.update(self.parameters())


def build_style_profile(palette_name: str) -> MatplotlibStyleProfile:
    return MatplotlibStyleProfile(palette=resolve_palette(palette_name))


STYLE_PROFILES: dict[str, str] = {
    "light": "light",
    "dark": "dark",
}


def resolve_style_profile(name: str) -> MatplotlibStyleProfile:
    if name in STYLE_PROFILES:
        return build_style_profile(STYLE_PROFILES[name])
    else:
        known = ", ".join(sorted(STYLE_PROFILES))
        raise KeyError(f"unknown style {name!r}, available: {known}")


DEFAULT_STYLE_PROFILE = MatplotlibStyleProfile(palette=LIGHT_PALETTE)
