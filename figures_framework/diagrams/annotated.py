from __future__ import annotations

from dataclasses import dataclass

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Circle, Ellipse, FancyBboxPatch

from ..context import FigureContext
from ..layout import (
    Extent,
    FigureScale,
    Point,
    evenly_spaced,
)
from ..schematics import TimelineEvent, TimelineLayout
from .base import DiagramNode, canvas_for_extent, square_canvas_for_extent


@dataclass(frozen=True)
class TimelineDiagram:
    events: list[TimelineEvent]
    layout: TimelineLayout = TimelineLayout.ALTERNATING
    spacing: float = 1.0
    scale: FigureScale = FigureScale(
        units_per_inch=0.78, vertical_units_per_inch=1.3
    )

    def positions(self) -> list[float]:
        return [
            event.position if event.position is not None else index
            * self.spacing
            for index, event in enumerate(self.events)
        ]

    def extent(self) -> Extent:
        positions = self.positions()
        span = max(positions) - min(positions)
        margin = max(span * 0.12, self.spacing)
        return Extent(
            left=min(positions) - margin,
            right=max(positions) + margin,
            bottom=-2.0,
            top=2.0,
        )

    def render(self, context: FigureContext) -> plt.Figure:
        canvas = canvas_for_extent(
            context, self.extent(), padding=0.2, scale=self.scale
        )
        canvas.draw_timeline(self.events, self.layout, self.spacing)
        return canvas.figure


@dataclass(frozen=True)
class SpectrumDiagram:
    marks: list[DiagramNode]
    ends: tuple[str, str]
    colormap: str = "Blues"
    width: float = 10.0
    scale: FigureScale = FigureScale(units_per_inch=0.92)

    def positions(self) -> list[float]:
        return list(
            np.linspace(-self.width / 2 + 0.5, self.width / 2 - 0.5,
                        len(self.marks))
        )

    def extent(self) -> Extent:
        return Extent(
            left=-self.width / 2 - 0.4,
            right=self.width / 2 + 0.4,
            bottom=-1.7,
            top=1.5,
        )

    def render(self, context: FigureContext) -> plt.Figure:
        canvas = canvas_for_extent(
            context, self.extent(), padding=0.2, scale=self.scale
        )
        gradient = np.linspace(0, 1, 256)[None, :]
        canvas.axes.imshow(
            gradient,
            extent=(-self.width / 2, self.width / 2, -0.3, 0.3),
            cmap=self.colormap,
            aspect="auto",
        )
        for mark, x in zip(self.marks, self.positions()):
            canvas.axes.plot([x, x], [0.3, 0.55], color=canvas.palette.ink,
                             lw=1.5)
            canvas.axes.text(x, 0.65, mark.label, ha="center", va="bottom",
                             fontsize=15)
            canvas.axes.text(x, -0.45, mark.caption, ha="center", va="top",
                             fontsize=13, color=canvas.palette.muted_ink)
        left_end, right_end = self.ends
        canvas.axes.text(
            -self.width / 2, -1.35, left_end, ha="left", fontsize=14,
            color=canvas.palette.blue, fontweight="bold",
        )
        canvas.axes.text(
            self.width / 2, -1.35, right_end, ha="right", fontsize=14,
            color=canvas.palette.ink, fontweight="bold",
        )
        return canvas.figure


@dataclass(frozen=True)
class FunnelDiagram:
    steps: list[DiagramNode]
    edge_captions: list[str]
    spacing: float = 3.4
    box_width: float = 2.0
    note: str = ""
    scale: FigureScale = FigureScale(units_per_inch=1.15)

    def heights(self) -> list[float]:
        count = len(self.steps)
        return [3.0 * (0.72 ** index) for index in range(count)]

    def positions(self) -> list[float]:
        return evenly_spaced(len(self.steps), self.spacing)

    def extent(self) -> Extent:
        tallest = max(self.heights())
        return Extent(
            left=min(self.positions()) - self.box_width,
            right=max(self.positions()) + self.box_width,
            bottom=-tallest / 2 - (1.6 if self.note else 0.6),
            top=tallest / 2 + 0.9,
        )

    def render(self, context: FigureContext) -> plt.Figure:
        extent = self.extent()
        canvas = canvas_for_extent(
            context, extent, padding=0.3, scale=self.scale
        )
        positions = self.positions()
        for step, x, height in zip(self.steps, positions, self.heights()):
            canvas.axes.add_patch(
                FancyBboxPatch(
                    (x - self.box_width / 2, -height / 2),
                    self.box_width,
                    height,
                    boxstyle="round,pad=0.05",
                    facecolor=step.color,
                    edgecolor="none",
                )
            )
            canvas.label((x, 0.0), step.label, "white", 18.0)
        for start, end, caption in zip(
            positions, positions[1:], self.edge_captions
        ):
            canvas.draw_arrow(
                (start + self.box_width / 2 + 0.1, 0.0),
                (end - self.box_width / 2 - 0.1, 0.0),
            )
            canvas.axes.text(
                (start + end) / 2, 0.35, caption, ha="center", fontsize=13,
                color=canvas.palette.muted_ink,
            )
        if self.note:
            canvas.axes.text(
                0, extent.bottom + 0.4, self.note, ha="center", fontsize=14,
                color=canvas.palette.muted_ink,
            )
        return canvas.figure


@dataclass(frozen=True)
class MappingDiagram:
    symbols: list[str]
    values: list[int]
    domain_label: str
    codomain_label: str
    note: str = ""

    def extent(self) -> Extent:
        return Extent(left=-5.6, right=6.6, bottom=-2.6, top=3.1)

    def render(self, context: FigureContext) -> plt.Figure:
        canvas = canvas_for_extent(context, self.extent(), padding=0.2)
        canvas.axes.add_patch(
            Ellipse((-3, 0), 4.4, 4.4, facecolor="#eef3fb",
                    edgecolor=canvas.palette.blue, lw=2)
        )
        canvas.axes.text(-3, 2.5, self.domain_label, ha="center", fontsize=18)
        canvas.axes.plot(
            [min(self.values), max(self.values)], [0, 0],
            color=canvas.palette.ink, lw=2,
        )
        for value in self.values:
            canvas.axes.plot([value, value], [-0.12, 0.12],
                             color=canvas.palette.ink, lw=2)
            canvas.axes.text(value, -0.55, str(value), ha="center",
                             fontsize=16)
        for index, (symbol, value) in enumerate(zip(self.symbols,
                                                    self.values)):
            position = self._symbol_position(index)
            canvas.axes.text(
                *position, symbol, ha="center", va="center", fontsize=34,
                family="DejaVu Sans",
            )
            canvas.draw_arrow(
                (position[0] + 0.35, position[1]),
                (value, 0.2),
                color=canvas.palette.blue if index % 2
                else canvas.palette.orange,
                curve=-0.2,
            )
        canvas.axes.text(3.5, -1.5, self.codomain_label, ha="center",
                         fontsize=22)
        if self.note:
            canvas.axes.text(0.3, 2.3, self.note, ha="center", fontsize=24)
        return canvas.figure

    def _symbol_position(self, index: int) -> Point:
        column = index % 2
        row = index // 2
        return (-3.9 + column * 1.75, 1.15 - row * 1.2)


@dataclass(frozen=True)
class SequenceDiagram:
    length: int
    highlighted: tuple[int, int]
    label_template: str = "$S_{{{index}}}$"
    span_caption: str = ""
    note: str = ""

    def extent(self) -> Extent:
        return Extent(
            left=0.2, right=self.length + 0.8,
            bottom=-1.7 if self.note else -1.0, top=1.7,
        )

    def render(self, context: FigureContext) -> plt.Figure:
        canvas = square_canvas_for_extent(context, self.extent(), padding=0.1)
        first, last = self.highlighted
        for rank in range(1, self.length + 1):
            inside = first <= rank <= last
            endpoint = rank in (first, last)
            color = canvas.palette.orange if endpoint else (
                canvas.palette.blue if inside else canvas.palette.grid
            )
            canvas.axes.add_patch(Circle((rank, 0), 0.38, color=color))
            canvas.axes.text(
                rank, 0, self.label_template.format(index=rank), ha="center",
                va="center", fontsize=13,
                color="white" if inside else canvas.palette.muted_ink,
            )
        canvas.axes.annotate(
            "", xy=(first - 0.4, 0.9), xytext=(last + 0.4, 0.9),
            arrowprops={"arrowstyle": "<->", "color": canvas.palette.ink},
        )
        middle = (first + last) / 2
        if self.span_caption:
            canvas.axes.text(middle, 1.15, self.span_caption, ha="center",
                             fontsize=15)
        if self.note:
            canvas.axes.text(middle, -1.2, self.note, ha="center", fontsize=15)
        return canvas.figure


@dataclass(frozen=True)
class EquationTermsDiagram:
    terms: list[DiagramNode]
    note: str = ""
    spacing: float = 1.25

    def positions(self) -> list[float]:
        widths = [0.45 + 0.28 * len(term.label) for term in self.terms]
        positions, cursor = [], 0.0
        for width in widths:
            positions.append(cursor + width / 2)
            cursor += width + self.spacing
        middle = cursor / 2
        return [position - middle for position in positions]

    def extent(self) -> Extent:
        positions = self.positions()
        return Extent(
            left=min(positions) - 1.2,
            right=max(positions) + 1.2,
            bottom=-2.2 if self.note else -1.6,
            top=1.4,
        )

    def render(self, context: FigureContext) -> plt.Figure:
        extent = self.extent()
        canvas = canvas_for_extent(context, extent, padding=0.2)
        for term, x in zip(self.terms, self.positions()):
            canvas.axes.text(x, 0.4, term.label, ha="center", va="center",
                             fontsize=34, color=term.color)
            if term.caption:
                canvas.axes.text(x, -1.0, term.caption, ha="center", va="top",
                                 fontsize=14, color=term.color)
            else:
                continue
        if self.note:
            canvas.axes.text(0, extent.bottom + 0.2, self.note, ha="center",
                             fontsize=15, color=canvas.palette.ink)
        return canvas.figure


@dataclass(frozen=True)
class NestedSetsDiagram:
    outer_label: str
    inner_label: str
    gap_label: str
    inputs: list[DiagramNode]
    note: str = ""

    def extent(self) -> Extent:
        return Extent(left=-5.6, right=5.6, bottom=-3.0, top=3.3)

    def render(self, context: FigureContext) -> plt.Figure:
        canvas = square_canvas_for_extent(context, self.extent(), padding=0.1)
        for index, node in enumerate(self.inputs):
            y = 1.5 - index * 1.5
            canvas.draw_box((-4.2, y), node.label, node.color)
            canvas.draw_arrow((-3.0, y * 0.8), (-0.6, y * 0.2))
        canvas.axes.add_patch(
            Circle((2.6, 0), 2.6, facecolor="#fde7dd",
                   edgecolor=canvas.palette.orange, lw=2)
        )
        canvas.axes.add_patch(
            Circle((2.0, 0), 1.6, facecolor="#dbe8f8",
                   edgecolor=canvas.palette.blue, lw=2)
        )
        canvas.label((2.0, 0.0), self.inner_label, canvas.palette.ink)
        canvas.axes.text(4.35, 0.15, self.gap_label, ha="center", va="center",
                         fontsize=12, color=canvas.palette.orange)
        canvas.axes.text(2.6, 2.85, self.outer_label, ha="center", fontsize=14,
                         color=canvas.palette.orange)
        if self.note:
            canvas.axes.text(-4.2, -2.7, self.note, ha="center", fontsize=15,
                             color=canvas.palette.muted_ink)
        return canvas.figure
