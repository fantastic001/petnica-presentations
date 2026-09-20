from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum

import matplotlib.pyplot as plt

from ..context import FigureContext
from ..layout import Extent, Point
from ..schematics import BoxSize, point_between
from .base import DiagramNode, canvas_for_extent, square_canvas_for_extent

BOX_MARGIN = 0.9


class CycleLayout(Enum):
    RING = "ring"
    COLUMNS = "columns"


@dataclass(frozen=True)
class CycleDiagram:
    steps: list[DiagramNode]
    layout: CycleLayout = CycleLayout.RING
    box_size: BoxSize = BoxSize(2.5, 1.1)
    center_note: str = ""
    side_notes: tuple[str, str] = ("", "")

    def radius(self) -> float:
        span = len(self.steps) * (self.box_size.width + BOX_MARGIN)
        return max(3.0, span / (2 * math.pi))

    def positions(self) -> list[Point]:
        match self.layout:
            case CycleLayout.RING:
                return self._ring_positions()
            case CycleLayout.COLUMNS:
                return self._column_positions()

    def extent(self) -> Extent:
        points = self.positions()
        half_width = self.box_size.width / 2
        half_height = self.box_size.height / 2
        return Extent(
            left=min(x for x, _ in points) - half_width,
            right=max(x for x, _ in points) + half_width,
            bottom=min(y for _, y in points) - half_height,
            top=max(y for _, y in points) + half_height,
        )

    def render(self, context: FigureContext) -> plt.Figure:
        padding = 1.4 if any(self.side_notes) else 0.6
        canvas = self._build_canvas(context, padding)
        centers = self.positions()
        for step, center in zip(self.steps, centers):
            canvas.draw_box(center, step.label, step.color, self.box_size)
        for index, start in enumerate(centers):
            end = centers[(index + 1) % len(centers)]
            canvas.draw_arrow(
                point_between(start, end, 0.33),
                point_between(start, end, 0.67),
            )
        self._draw_notes(canvas)
        return canvas.figure

    def _build_canvas(self, context: FigureContext, padding: float):
        match self.layout:
            case CycleLayout.RING:
                return square_canvas_for_extent(
                    context, self.extent(), padding
                )
            case CycleLayout.COLUMNS:
                return canvas_for_extent(context, self.extent(), padding)

    def _ring_positions(self) -> list[Point]:
        radius = self.radius()
        count = len(self.steps)
        angles = [
            math.pi / 2 - 2 * math.pi * index / count for index in range(count)
        ]
        return [
            (radius * math.cos(angle), radius * math.sin(angle))
            for angle in angles
        ]

    def _column_positions(self) -> list[Point]:
        count = len(self.steps)
        if count < 4 or count % 2:
            raise ValueError("column layout needs an even count of at least 4")
        else:
            per_column = (count - 2) // 2
            step = self.box_size.height + 0.9
            column = self.box_size.width / 2 + 1.7
            levels = [
                step * (per_column - 1) / 2 - index * step
                for index in range(per_column)
            ]
            apex = max(levels) + step
            left = [(-column, level) for level in levels]
            right = [(column, level) for level in reversed(levels)]
            return [(0.0, apex)] + left + [(0.0, -apex)] + right

    def _draw_notes(self, canvas) -> None:
        extent = self.extent()
        if self.center_note:
            canvas.label(
                (0.0, 0.0), self.center_note, canvas.palette.muted_ink, 20.0
            )
        left_note, right_note = self.side_notes
        for note, x, color in [
            (left_note, extent.left - 0.9, canvas.palette.orange),
            (right_note, extent.right + 0.9, canvas.palette.violet),
        ]:
            if note:
                canvas.axes.text(
                    x, 0, note, rotation=90, ha="center", va="center",
                    color=color, fontsize=16, fontweight="bold",
                )
            else:
                continue
