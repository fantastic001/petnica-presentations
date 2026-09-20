from __future__ import annotations

from dataclasses import dataclass

import matplotlib.pyplot as plt

from ..context import FigureContext
from ..layout import (
    CaptionPlacement,
    FigureScale,
    Extent,
    Orientation,
    Point,
    evenly_spaced,
)
from ..schematics import BoxSize, SchematicCanvas
from .base import DiagramNode, canvas_for_extent

CAPTION_GAP = 0.35
CAPTION_HEIGHT = 1.2
ORIGIN: Point = (0.0, 0.0)


def shifted(point: Point, origin: Point) -> Point:
    return (point[0] + origin[0], point[1] + origin[1])


@dataclass(frozen=True)
class FlowDiagram:
    steps: list[DiagramNode]
    orientation: Orientation = Orientation.HORIZONTAL
    box_size: BoxSize = BoxSize(2.6, 1.2)
    spacing: float = 3.4
    caption_placement: CaptionPlacement = CaptionPlacement.BELOW
    note: str = ""
    feedback: str = ""

    def positions(self) -> list[Point]:
        offsets = evenly_spaced(len(self.steps), self.spacing)
        match self.orientation:
            case Orientation.HORIZONTAL:
                return [(offset, 0.0) for offset in offsets]
            case Orientation.VERTICAL:
                return [(0.0, -offset) for offset in offsets]

    def extent(self) -> Extent:
        points = self.positions()
        extent = Extent(
            left=min(x for x, _ in points) - self.box_size.width / 2,
            right=max(x for x, _ in points) + self.box_size.width / 2,
            bottom=min(y for _, y in points) - self.box_size.height / 2,
            top=max(y for _, y in points) + self.box_size.height / 2,
        )
        below = CAPTION_HEIGHT * sum(
            [self._has_captions(), bool(self.note or self.feedback)]
        )
        return Extent(extent.left, extent.right, extent.bottom - below,
                      extent.top)

    def draw(
        self, canvas: SchematicCanvas, origin: Point = ORIGIN
    ) -> list[Point]:
        centers = [shifted(point, origin) for point in self.positions()]
        for step, center in zip(self.steps, centers):
            canvas.draw_box(center, step.label, step.color, self.box_size)
        for start, end in zip(centers, centers[1:]):
            canvas.draw_arrow(*self._arrow_ends(start, end))
        self._draw_captions(canvas, centers)
        self._draw_notes(canvas, centers, origin)
        return centers

    def render(self, context: FigureContext) -> plt.Figure:
        canvas = canvas_for_extent(context, self.extent())
        self.draw(canvas)
        return canvas.figure

    def _has_captions(self) -> bool:
        captioned = any(step.caption for step in self.steps)
        return captioned and self.caption_placement is not CaptionPlacement.NONE

    def _arrow_ends(self, start: Point, end: Point) -> tuple[Point, Point]:
        match self.orientation:
            case Orientation.HORIZONTAL:
                gap = self.box_size.width / 2 + 0.08
                return ((start[0] + gap, start[1]), (end[0] - gap, end[1]))
            case Orientation.VERTICAL:
                gap = self.box_size.height / 2 + 0.08
                return ((start[0], start[1] - gap), (end[0], end[1] + gap))

    def _draw_captions(
        self, canvas: SchematicCanvas, centers: list[Point]
    ) -> None:
        if self._has_captions():
            below = self.caption_placement is CaptionPlacement.BELOW
            direction = -1 if below else 1
            offset = self.box_size.height / 2 + CAPTION_GAP
            for step, (x, y) in zip(self.steps, centers):
                if step.caption:
                    canvas.axes.text(
                        x, y + direction * offset, step.caption, ha="center",
                        va="top" if below else "bottom", fontsize=13,
                        color=canvas.palette.muted_ink,
                    )
                else:
                    continue
        else:
            return

    def _draw_notes(
        self, canvas: SchematicCanvas, centers: list[Point], origin: Point
    ) -> None:
        bottom = self.extent().bottom + origin[1]
        middle = (centers[0][0] + centers[-1][0]) / 2
        if self.feedback:
            level = bottom + 0.6
            canvas.draw_arrow(
                (centers[-1][0], centers[-1][1] - self.box_size.height / 2),
                (centers[0][0], level),
                color=canvas.palette.aqua,
                curve=-0.35,
            )
            canvas.axes.text(
                middle, level - 0.55, self.feedback, ha="center", fontsize=14,
                color=canvas.palette.aqua,
            )
        if self.note:
            canvas.axes.text(
                middle, bottom + 0.1, self.note, ha="center", va="bottom",
                fontsize=15, color=canvas.palette.ink,
            )


@dataclass(frozen=True)
class MergeFlowDiagram:
    inputs: list[DiagramNode]
    process: DiagramNode
    output: DiagramNode
    box_size: BoxSize = BoxSize(2.0, 0.8)
    spacing: float = 3.0

    def input_positions(self) -> list[Point]:
        levels = evenly_spaced(len(self.inputs), self.box_size.height + 0.6)
        return [(-self.spacing, level) for level in reversed(levels)]

    def extent(self) -> Extent:
        points = self.input_positions() + [(self.spacing, 0.0)]
        return Extent(
            left=min(x for x, _ in points) - self.box_size.width / 2,
            right=max(x for x, _ in points) + self.box_size.width / 2,
            bottom=min(y for _, y in points) - self.box_size.height,
            top=max(y for _, y in points) + self.box_size.height,
        )

    def draw(self, canvas: SchematicCanvas, origin: Point = ORIGIN) -> None:
        process_center = shifted((0.0, 0.0), origin)
        canvas.draw_box(
            process_center, self.process.label, self.process.color,
            BoxSize(self.box_size.width, self.box_size.height + 0.2),
        )
        for node, point in zip(self.inputs, self.input_positions()):
            center = shifted(point, origin)
            canvas.draw_box(center, node.label, node.color, self.box_size)
            canvas.draw_arrow(
                (center[0] + self.box_size.width / 2 + 0.05, center[1]),
                (process_center[0] - self.box_size.width / 2 - 0.05,
                 process_center[1] + (center[1] - process_center[1]) * 0.25),
            )
        output_center = shifted((self.spacing, 0.0), origin)
        canvas.draw_box(
            output_center, self.output.label, self.output.color, self.box_size
        )
        canvas.draw_arrow(
            (process_center[0] + self.box_size.width / 2 + 0.05,
             process_center[1]),
            (output_center[0] - self.box_size.width / 2 - 0.05,
             output_center[1]),
        )

    def render(self, context: FigureContext) -> plt.Figure:
        canvas = canvas_for_extent(context, self.extent())
        self.draw(canvas)
        return canvas.figure


@dataclass(frozen=True)
class StackedDiagrams:
    rows: list[tuple[str, MergeFlowDiagram | FlowDiagram]]
    row_spacing: float = 3.6
    label_width: float = 2.6
    scale: FigureScale = FigureScale(
        units_per_inch=1.2, vertical_units_per_inch=1.58
    )

    def extent(self) -> Extent:
        merged = self.rows[0][1].extent()
        for _, diagram in self.rows[1:]:
            merged = merged.merged(diagram.extent())
        offsets = self._offsets()
        return Extent(
            left=merged.left - self.label_width,
            right=merged.right,
            bottom=min(offsets) + merged.bottom,
            top=max(offsets) + merged.top,
        )

    def render(self, context: FigureContext) -> plt.Figure:
        extent = self.extent()
        canvas = canvas_for_extent(
            context, extent, padding=0.3, scale=self.scale
        )
        for (title, diagram), offset in zip(self.rows, self._offsets()):
            diagram.draw(canvas, (0.0, offset))
            canvas.axes.text(
                extent.left + self.label_width / 2, offset, title,
                ha="center", va="center", fontsize=15,
                color=canvas.palette.ink,
            )
        self._draw_separators(canvas, extent)
        return canvas.figure

    def _offsets(self) -> list[float]:
        return evenly_spaced(len(self.rows), self.row_spacing)[::-1]

    def _draw_separators(self, canvas: SchematicCanvas, extent: Extent) -> None:
        offsets = self._offsets()
        for upper, lower in zip(offsets, offsets[1:]):
            canvas.axes.plot(
                [extent.left, extent.right],
                [(upper + lower) / 2, (upper + lower) / 2],
                color=canvas.palette.grid, lw=2,
            )
