from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum

import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch

from .palette import Palette

Point = tuple[float, float]


class Aspect(Enum):
    AUTO = "auto"
    EQUAL = "equal"


class TimelineLayout(Enum):
    ALTERNATING = "alternating"
    ABOVE = "above"


@dataclass(frozen=True)
class BoxSize:
    width: float = 2.2
    height: float = 0.9


@dataclass(frozen=True)
class ChainStep:
    label: str
    color: str


@dataclass(frozen=True)
class TimelineEvent:
    label: str
    caption: str
    color: str
    position: float | None = None


DEFAULT_BOX_SIZE = BoxSize()


def point_between(start: Point, end: Point, fraction: float) -> Point:
    return (
        start[0] + (end[0] - start[0]) * fraction,
        start[1] + (end[1] - start[1]) * fraction,
    )


def circular_positions(count: int, radius: float) -> list[Point]:
    angles = [
        math.pi / 2 - 2 * math.pi * index / count for index in range(count)
    ]
    return [(radius * math.cos(a), radius * math.sin(a)) for a in angles]


class SchematicCanvas:
    def __init__(self, palette: Palette, size: tuple[float, float]) -> None:
        self.palette = palette
        self.figure, self.axes = plt.subplots(figsize=size)
        self.axes.set_axis_off()
        self.axes.grid(False)

    def draw_box(
        self,
        center: Point,
        text: str,
        color: str,
        size: BoxSize = DEFAULT_BOX_SIZE,
    ) -> None:
        x, y = center
        self.axes.add_patch(
            FancyBboxPatch(
                (x - size.width / 2, y - size.height / 2),
                size.width,
                size.height,
                boxstyle="round,pad=0.05,rounding_size=0.18",
                facecolor=color,
                edgecolor="none",
            )
        )
        self.axes.text(
            x,
            y,
            text,
            ha="center",
            va="center",
            color="white",
            fontsize=15,
            fontweight="bold",
        )

    def draw_arrow(
        self,
        start: Point,
        end: Point,
        color: str | None = None,
        curve: float = 0.0,
    ) -> None:
        self.axes.add_patch(
            FancyArrowPatch(
                start,
                end,
                arrowstyle="-|>",
                mutation_scale=22,
                color=color or self.palette.muted_ink,
                linewidth=2,
                connectionstyle=f"arc3,rad={curve}",
            )
        )

    def draw_circle(self, center: Point, radius: float, color: str) -> None:
        self.axes.add_patch(Circle(center, radius, color=color, zorder=2))

    def label(
        self,
        position: Point,
        text: str,
        color: str | None = None,
        size: float = 15.0,
    ) -> None:
        self.axes.text(
            position[0],
            position[1],
            text,
            ha="center",
            va="center",
            color=color or self.palette.ink,
            fontsize=size,
        )

    def draw_chain(
        self,
        steps: list[ChainStep],
        spacing: float = 3.0,
        size: BoxSize = DEFAULT_BOX_SIZE,
    ) -> list[Point]:
        offset = spacing * (len(steps) - 1) / 2
        centers = [
            (index * spacing - offset, 0.0) for index in range(len(steps))
        ]
        for step, center in zip(steps, centers):
            self.draw_box(center, step.label, step.color, size)
        for start, end in zip(centers, centers[1:]):
            self.draw_arrow(
                (start[0] + size.width / 2 + 0.05, 0.0),
                (end[0] - size.width / 2 - 0.05, 0.0),
            )
        return centers

    def draw_cycle(
        self,
        steps: list[ChainStep],
        radius: float = 3.9,
        size: BoxSize = DEFAULT_BOX_SIZE,
    ) -> list[Point]:
        centers = circular_positions(len(steps), radius)
        for step, center in zip(steps, centers):
            self.draw_box(center, step.label, step.color, size)
        for index, start in enumerate(centers):
            end = centers[(index + 1) % len(centers)]
            self.draw_arrow(
                point_between(start, end, 0.33),
                point_between(start, end, 0.67),
            )
        return centers

    def draw_timeline(
        self,
        events: list[TimelineEvent],
        layout: TimelineLayout = TimelineLayout.ALTERNATING,
        spacing: float = 1.0,
    ) -> None:
        positions = [
            event.position if event.position is not None else index * spacing
            for index, event in enumerate(events)
        ]
        margin = spacing * 0.6
        self.axes.plot(
            [min(positions) - margin, max(positions) + margin],
            [0, 0],
            color=self.palette.ink,
            lw=2,
        )
        for index, (event, position) in enumerate(zip(events, positions)):
            side = self._timeline_side(layout, index)
            self.axes.scatter(position, 0, s=170, color=event.color, zorder=3)
            self.axes.plot(
                [position, position], [0, 0.55 * side], color=event.color,
                lw=1.5,
            )
            self.axes.text(
                position,
                0.7 * side,
                event.label,
                ha="center",
                va="bottom" if side > 0 else "top",
                fontsize=15,
            )
            self.axes.text(
                position,
                -0.28 * side,
                event.caption,
                ha="center",
                va="top" if side > 0 else "bottom",
                fontsize=13,
                color=self.palette.muted_ink,
            )

    def _timeline_side(self, layout: TimelineLayout, index: int) -> int:
        match layout:
            case TimelineLayout.ABOVE:
                return 1
            case TimelineLayout.ALTERNATING:
                return 1 if index % 2 == 0 else -1

    def set_bounds(
        self,
        x_range: tuple[float, float],
        y_range: tuple[float, float],
        aspect: Aspect = Aspect.AUTO,
    ) -> None:
        self.axes.set_xlim(*x_range)
        self.axes.set_ylim(*y_range)
        self.axes.set_aspect(aspect.value)
