from __future__ import annotations

from .cli import render_registry
from .context import (
    DEFAULT_DIAGRAM_SIZE,
    DEFAULT_WIDE_SIZE,
    FigureContext,
    GridSpecification,
)
from .mathtools import (
    binomial_pmf,
    fit_polynomial,
    harmonic_number,
    logarithmic_sample,
    normal_pdf,
    poisson_pmf,
    polynomial_features,
)
from .output import FigureWriter, OutputFormat
from .palette import DARK_PALETTE, LIGHT_PALETTE, Palette
from .registry import FigureRegistry, FigureSpecification
from .runner import FigureRunner, RenderReport
from .schematics import (
    Aspect,
    BoxSize,
    ChainStep,
    SchematicCanvas,
    TimelineEvent,
    TimelineLayout,
    circular_positions,
    point_between,
)
from .settings import RenderMode, RenderSettings, environment_integer
from .style import (
    MatplotlibStyleProfile,
    TypographyScale,
    resolve_style_profile,
)

__all__ = [
    "Aspect",
    "BoxSize",
    "ChainStep",
    "DARK_PALETTE",
    "DEFAULT_DIAGRAM_SIZE",
    "DEFAULT_WIDE_SIZE",
    "FigureContext",
    "FigureRegistry",
    "FigureRunner",
    "FigureSpecification",
    "FigureWriter",
    "GridSpecification",
    "LIGHT_PALETTE",
    "MatplotlibStyleProfile",
    "OutputFormat",
    "Palette",
    "RenderMode",
    "RenderReport",
    "RenderSettings",
    "SchematicCanvas",
    "TimelineEvent",
    "TimelineLayout",
    "TypographyScale",
    "binomial_pmf",
    "circular_positions",
    "environment_integer",
    "fit_polynomial",
    "harmonic_number",
    "logarithmic_sample",
    "normal_pdf",
    "poisson_pmf",
    "point_between",
    "polynomial_features",
    "render_registry",
    "resolve_style_profile",
]
