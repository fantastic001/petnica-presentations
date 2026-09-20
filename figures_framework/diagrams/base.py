from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

import matplotlib.pyplot as plt

from ..context import FigureContext
from ..layout import DEFAULT_FIGURE_SCALE, Extent, FigureScale
from ..schematics import Aspect, SchematicCanvas


@dataclass(frozen=True)
class DiagramNode:
    label: str
    color: str
    caption: str = ""


class Diagram(Protocol):
    def render(self, context: FigureContext) -> plt.Figure:
        ...


def canvas_for_extent(
    context: FigureContext,
    extent: Extent,
    padding: float = 0.6,
    scale: FigureScale = DEFAULT_FIGURE_SCALE,
) -> SchematicCanvas:
    bounds = extent.padded(padding)
    canvas = context.blank_canvas(scale.size_for(bounds))
    canvas.set_bounds(bounds.x_range(), bounds.y_range())
    return canvas


def fit_canvas(canvas: SchematicCanvas, extent: Extent, padding: float) -> None:
    bounds = extent.padded(padding)
    canvas.set_bounds(bounds.x_range(), bounds.y_range())


def square_canvas_for_extent(
    context: FigureContext,
    extent: Extent,
    padding: float = 0.6,
    scale: FigureScale = DEFAULT_FIGURE_SCALE,
) -> SchematicCanvas:
    bounds = extent.padded(padding)
    canvas = context.blank_canvas(scale.size_for(bounds))
    canvas.set_bounds(bounds.x_range(), bounds.y_range(), Aspect.EQUAL)
    return canvas
