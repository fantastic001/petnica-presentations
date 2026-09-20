from __future__ import annotations

from dataclasses import dataclass

import matplotlib.pyplot as plt

from ..context import FigureContext
from ..layout import Extent
from ..schematics import BoxSize
from .base import DiagramNode, canvas_for_extent


@dataclass(frozen=True)
class SplitDiagram:
    source: DiagramNode
    splitter: DiagramNode
    groups: list[DiagramNode]
    sample_size: int = 24

    def extent(self) -> Extent:
        return Extent(left=-6.0, right=6.0, bottom=-4.0, top=3.8)

    def render(self, context: FigureContext) -> plt.Figure:
        canvas = canvas_for_extent(context, self.extent(), padding=0.2)
        cloud = context.random.uniform(
            [-5.3, -2], [-2.7, 2], size=(self.sample_size, 2)
        )
        canvas.axes.scatter(
            cloud[:, 0], cloud[:, 1], s=160, c=self.source.color
        )
        canvas.axes.text(-4, 2.6, self.source.label, ha="center", fontsize=16)
        canvas.draw_box(
            (0, 0), self.splitter.label, self.splitter.color, BoxSize(2.2, 1.3)
        )
        canvas.draw_arrow((-2.5, 0), (-1.2, 0))
        levels = [(1.0, 2.8, 3.2), (-2.8, -1.0, -3.5)]
        signs = [1, -1]
        for group, (low, high, caption_y), sign in zip(
            self.groups, levels, signs
        ):
            canvas.draw_arrow((1.2, 0.4 * sign), (2.4, 1.6 * sign))
            points = context.random.uniform(
                [2.6, low], [5.2, high], size=(self.sample_size // 2, 2)
            )
            canvas.axes.scatter(points[:, 0], points[:, 1], s=160,
                                c=group.color)
            canvas.axes.text(3.9, caption_y, group.label, ha="center",
                             color=group.color, fontsize=16)
        return canvas.figure
