from __future__ import annotations

from dataclasses import dataclass

import matplotlib.pyplot as plt

from ..context import FigureContext
from ..layout import Extent
from ..schematics import BoxSize
from .base import DiagramNode, canvas_for_extent


@dataclass(frozen=True)
class FeedbackLoopDiagram:
    controller: DiagramNode
    upper: DiagramNode
    lower: DiagramNode
    goal: DiagramNode | None = None
    edge_labels: tuple[str, str] = ("", "")
    note: str = ""

    def extent(self) -> Extent:
        top = 3.5 if self.goal else 2.4
        bottom = -3.6 if self.note else -2.6
        return Extent(left=-5.0, right=5.2, bottom=bottom, top=top)

    def render(self, context: FigureContext) -> plt.Figure:
        extent = self.extent()
        canvas = canvas_for_extent(context, extent, padding=0.3)
        controller_size = BoxSize(2.6, 1.4)
        satellite_size = BoxSize(3.4, 1.3)
        canvas.draw_box(
            (-3.0, 0.0), self.controller.label, self.controller.color,
            controller_size,
        )
        canvas.draw_box(
            (3.0, 1.6), self.upper.label, self.upper.color, satellite_size
        )
        canvas.draw_box(
            (3.0, -1.6), self.lower.label, self.lower.color, satellite_size
        )
        canvas.draw_arrow((-1.65, 0.5), (1.25, 1.5), curve=-0.2)
        canvas.draw_arrow((3.0, 0.9), (3.0, -0.9))
        canvas.draw_arrow((1.25, -1.5), (-1.65, -0.5), curve=-0.2)
        self._draw_goal(canvas)
        self._draw_labels(canvas, extent)
        return canvas.figure

    def _draw_goal(self, canvas) -> None:
        if self.goal is None:
            return
        else:
            canvas.draw_box(
                (-3.0, 2.9), self.goal.label, self.goal.color, BoxSize(1.8, 0.8)
            )
            canvas.draw_arrow((-3.0, 2.45), (-3.0, 0.75))

    def _draw_labels(self, canvas, extent: Extent) -> None:
        action, observation = self.edge_labels
        if action:
            canvas.label((-0.4, 1.75), action, canvas.palette.ink)
        if observation:
            canvas.label((-0.4, -1.85), observation, canvas.palette.ink)
        if self.note:
            canvas.axes.text(
                0, extent.bottom + 0.2, self.note, ha="center", va="bottom",
                fontsize=16, color=canvas.palette.muted_ink,
            )


@dataclass(frozen=True)
class VerificationLoopDiagram:
    producer: DiagramNode
    checker: DiagramNode
    accepted: DiagramNode
    rejected: DiagramNode
    note: str = ""

    def extent(self) -> Extent:
        return Extent(left=-5.5, right=6.0, bottom=-3.4, top=2.2)

    def render(self, context: FigureContext) -> plt.Figure:
        extent = self.extent()
        canvas = canvas_for_extent(context, extent, padding=0.3)
        canvas.draw_box(
            (-3.8, 0.0), self.producer.label, self.producer.color,
            BoxSize(3.0, 1.4),
        )
        canvas.draw_box(
            (0.6, 0.0), self.checker.label, self.checker.color,
            BoxSize(3.4, 1.4),
        )
        canvas.draw_box(
            (4.4, 1.3), self.accepted.label, self.accepted.color,
            BoxSize(2.4, 0.9),
        )
        canvas.draw_box(
            (4.4, -1.3), self.rejected.label, self.rejected.color,
            BoxSize(2.8, 0.9),
        )
        canvas.draw_arrow((-2.25, 0.0), (-1.15, 0.0))
        canvas.draw_arrow((2.35, 0.3), (3.15, 1.1))
        canvas.draw_arrow((2.35, -0.3), (3.0, -1.1))
        canvas.draw_arrow(
            (3.0, -1.75), (-3.8, -0.75), color=canvas.palette.red, curve=-0.35
        )
        if self.note:
            canvas.axes.text(
                -0.6, extent.bottom + 0.3, self.note, ha="center",
                fontsize=14, color=canvas.palette.red,
            )
        return canvas.figure
