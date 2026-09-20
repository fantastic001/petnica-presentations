from __future__ import annotations

from dataclasses import dataclass

import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

from ..context import FigureContext
from ..layout import Extent, Point
from ..schematics import BoxSize
from .base import DiagramNode, canvas_for_extent

LAYER_GAP = 0.7


@dataclass(frozen=True)
class RepeatedGroup:
    first: int
    last: int
    label: str


@dataclass(frozen=True)
class LayeredStackDiagram:
    layers: list[DiagramNode]
    box_size: BoxSize = BoxSize(4.4, 0.9)
    repeated: RepeatedGroup | None = None

    def positions(self) -> list[Point]:
        step = self.box_size.height + LAYER_GAP
        return [(0.0, index * step) for index in range(len(self.layers))]

    def extent(self) -> Extent:
        points = self.positions()
        width = max(self.box_size.width, 5.6)
        return Extent(
            left=-width / 2 - 0.9,
            right=width / 2 + 1.6,
            bottom=points[0][1] - self.box_size.height,
            top=points[-1][1] + self.box_size.height,
        )

    def render(self, context: FigureContext) -> plt.Figure:
        canvas = canvas_for_extent(context, self.extent())
        centers = self.positions()
        self._draw_group(canvas, centers)
        for layer, center in zip(self.layers, centers):
            canvas.draw_box(
                center, layer.label, layer.color,
                BoxSize(self._width_of(layer), self.box_size.height),
            )
        for start, end in zip(centers, centers[1:]):
            gap = self.box_size.height / 2 + 0.1
            canvas.draw_arrow(
                (start[0], start[1] + gap), (end[0], end[1] - gap)
            )
        return canvas.figure

    def _width_of(self, layer: DiagramNode) -> float:
        return max(self.box_size.width * 0.55, min(
            self.box_size.width, 0.28 * len(layer.label) + 1.6
        ))

    def _draw_group(self, canvas, centers: list[Point]) -> None:
        if self.repeated is None:
            return
        else:
            low = centers[self.repeated.first][1] - self.box_size.height
            high = centers[self.repeated.last][1] + self.box_size.height
            width = self.box_size.width + 1.0
            canvas.axes.add_patch(
                FancyBboxPatch(
                    (-width / 2, low),
                    width,
                    high - low,
                    boxstyle="round,pad=0.1",
                    facecolor="#eef3fb",
                    edgecolor=canvas.palette.blue,
                    lw=2,
                )
            )
            canvas.axes.text(
                width / 2 + 0.35,
                (low + high) / 2,
                self.repeated.label,
                fontsize=22,
                color=canvas.palette.blue,
                fontweight="bold",
                va="center",
            )


@dataclass(frozen=True)
class LayeredNetworkDiagram:
    layer_sizes: list[int]
    layer_colors: list[str]
    layer_labels: list[str]
    node_radius: float = 0.32
    horizontal_spacing: float = 3.0
    vertical_spacing: float = 1.1
    note: str = ""

    def positions(self) -> list[list[Point]]:
        layers = []
        for index, size in enumerate(self.layer_sizes):
            x = index * self.horizontal_spacing
            offset = (size - 1) / 2
            layers.append(
                [
                    (x, (position - offset) * self.vertical_spacing)
                    for position in range(size)
                ]
            )
        return layers

    def extent(self) -> Extent:
        layers = self.positions()
        flat = [point for layer in layers for point in layer]
        return Extent(
            left=min(x for x, _ in flat) - 1.0,
            right=max(x for x, _ in flat) + 1.0,
            bottom=min(y for _, y in flat) - 1.4,
            top=max(y for _, y in flat) + (1.6 if self.note else 0.8),
        )

    def render(self, context: FigureContext) -> plt.Figure:
        extent = self.extent()
        canvas = canvas_for_extent(context, extent)
        layers = self.positions()
        for left, right in zip(layers, layers[1:]):
            for start in left:
                for end in right:
                    canvas.axes.plot(
                        [start[0], end[0]], [start[1], end[1]],
                        color=canvas.palette.grid, lw=1.2, zorder=1,
                    )
        for layer, color in zip(layers, self.layer_colors):
            for point in layer:
                canvas.draw_circle(point, self.node_radius, color)
        self._draw_labels(canvas, layers, extent)
        return canvas.figure

    def _draw_labels(self, canvas, layers, extent: Extent) -> None:
        for label, layer in zip(self.layer_labels, layers):
            if label:
                canvas.axes.text(
                    layer[0][0], extent.bottom + 0.4, label, ha="center",
                    fontsize=15, color=canvas.palette.muted_ink,
                )
            else:
                continue
        if self.note:
            middle = (extent.left + extent.right) / 2
            canvas.axes.text(
                middle, extent.top - 0.4, self.note, ha="center",
                fontsize=16, color=canvas.palette.ink,
            )
