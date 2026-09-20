from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

Point = tuple[float, float]


class Orientation(Enum):
    HORIZONTAL = "horizontal"
    VERTICAL = "vertical"


class CaptionPlacement(Enum):
    BELOW = "below"
    ABOVE = "above"
    NONE = "none"


class Side(Enum):
    LEFT = "left"
    RIGHT = "right"
    TOP = "top"
    BOTTOM = "bottom"

    def unit_vector(self) -> Point:
        match self:
            case Side.LEFT:
                return (-1.0, 0.0)
            case Side.RIGHT:
                return (1.0, 0.0)
            case Side.TOP:
                return (0.0, 1.0)
            case Side.BOTTOM:
                return (0.0, -1.0)


@dataclass(frozen=True)
class Extent:
    left: float
    right: float
    bottom: float
    top: float

    def width(self) -> float:
        return self.right - self.left

    def height(self) -> float:
        return self.top - self.bottom

    def padded(self, padding: float) -> "Extent":
        return Extent(
            left=self.left - padding,
            right=self.right + padding,
            bottom=self.bottom - padding,
            top=self.top + padding,
        )

    def merged(self, other: "Extent") -> "Extent":
        return Extent(
            left=min(self.left, other.left),
            right=max(self.right, other.right),
            bottom=min(self.bottom, other.bottom),
            top=max(self.top, other.top),
        )

    def x_range(self) -> tuple[float, float]:
        return (self.left, self.right)

    def y_range(self) -> tuple[float, float]:
        return (self.bottom, self.top)


def extent_of_points(points: list[Point]) -> Extent:
    if not points:
        raise ValueError("cannot compute extent of an empty point list")
    else:
        xs = [x for x, _ in points]
        ys = [y for _, y in points]
        return Extent(min(xs), max(xs), min(ys), max(ys))


def evenly_spaced(count: int, spacing: float) -> list[float]:
    offset = spacing * (count - 1) / 2
    return [index * spacing - offset for index in range(count)]


@dataclass(frozen=True)
class FigureScale:
    units_per_inch: float = 1.25
    vertical_units_per_inch: float | None = None
    minimum: tuple[float, float] = (5.0, 2.6)
    maximum: tuple[float, float] = (13.0, 8.4)

    def vertical_scale(self) -> float:
        if self.vertical_units_per_inch is None:
            return self.units_per_inch
        else:
            return self.vertical_units_per_inch

    def size_for(self, extent: Extent) -> tuple[float, float]:
        width = extent.width() / self.units_per_inch
        height = extent.height() / self.vertical_scale()
        return (
            min(max(width, self.minimum[0]), self.maximum[0]),
            min(max(height, self.minimum[1]), self.maximum[1]),
        )


DEFAULT_FIGURE_SCALE = FigureScale()
