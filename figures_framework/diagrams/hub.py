from __future__ import annotations

from dataclasses import dataclass

import matplotlib.pyplot as plt

from ..context import FigureContext
from ..layout import Extent, Point, Side
from ..schematics import BoxSize
from .base import DiagramNode, canvas_for_extent

SATELLITE_DISTANCE = 4.0


@dataclass(frozen=True)
class HubSatellite:
    node: DiagramNode
    side: Side
    size: BoxSize = BoxSize(2.8, 1.3)


@dataclass(frozen=True)
class HubDiagram:
    center: DiagramNode
    satellites: list[HubSatellite]
    center_size: BoxSize = BoxSize(2.4, 1.6)
    distance: float = SATELLITE_DISTANCE
    note: str = ""

    def position_of(self, satellite: HubSatellite) -> Point:
        dx, dy = satellite.side.unit_vector()
        return (dx * self.distance, dy * self.distance * 0.65)

    def extent(self) -> Extent:
        points = [(0.0, 0.0)] + [
            self.position_of(satellite) for satellite in self.satellites
        ]
        widths = [self.center_size.width] + [
            satellite.size.width for satellite in self.satellites
        ]
        heights = [self.center_size.height] + [
            satellite.size.height for satellite in self.satellites
        ]
        half_width = max(widths) / 2
        half_height = max(heights) / 2
        extent = Extent(
            left=min(x for x, _ in points) - half_width,
            right=max(x for x, _ in points) + half_width,
            bottom=min(y for _, y in points) - half_height,
            top=max(y for _, y in points) + half_height,
        )
        if self.note:
            return Extent(
                extent.left, extent.right, extent.bottom - 1.1, extent.top
            )
        else:
            return extent

    def render(self, context: FigureContext) -> plt.Figure:
        extent = self.extent()
        canvas = canvas_for_extent(context, extent)
        canvas.draw_box(
            (0.0, 0.0), self.center.label, self.center.color, self.center_size
        )
        for satellite in self.satellites:
            self._draw_satellite(canvas, satellite)
        if self.note:
            canvas.axes.text(
                0, extent.bottom + 0.2, self.note, ha="center", va="bottom",
                fontsize=22, color=canvas.palette.ink,
            )
        return canvas.figure

    def _draw_satellite(self, canvas, satellite: HubSatellite) -> None:
        position = self.position_of(satellite)
        canvas.draw_box(
            position, satellite.node.label, satellite.node.color,
            satellite.size,
        )
        canvas.draw_arrow(*self._arrow_ends(satellite, position))

    def _arrow_ends(
        self, satellite: HubSatellite, position: Point
    ) -> tuple[Point, Point]:
        dx, dy = satellite.side.unit_vector()
        start = (
            position[0] - dx * (satellite.size.width / 2 + 0.1),
            position[1] - dy * (satellite.size.height / 2 + 0.1),
        )
        end = (
            dx * (self.center_size.width / 2 + 0.15),
            dy * (self.center_size.height / 2 + 0.15),
        )
        match satellite.side:
            case Side.LEFT | Side.RIGHT:
                return (start, end)
            case Side.TOP | Side.BOTTOM:
                return (start, end)
