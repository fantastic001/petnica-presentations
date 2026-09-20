from __future__ import annotations

from collections.abc import Collection, Iterator
from dataclasses import dataclass
from typing import Callable, Protocol

import matplotlib.pyplot as plt


class FigureContextProtocol(Protocol):
    pass


FigureRenderer = Callable[["FigureContext"], plt.Figure]


@dataclass(frozen=True)
class FigureSpecification:
    name: str
    render: FigureRenderer


class FigureRegistry:
    def __init__(self, name: str) -> None:
        self.name = name
        self._specifications: dict[str, FigureSpecification] = {}

    def register(self, name: str) -> Callable[[FigureRenderer], FigureRenderer]:
        def decorate(renderer: FigureRenderer) -> FigureRenderer:
            self.add(FigureSpecification(name=name, render=renderer))
            return renderer

        return decorate

    def add(self, specification: FigureSpecification) -> None:
        if specification.name in self._specifications:
            raise KeyError(
                f"figure {specification.name!r} already registered in "
                f"{self.name!r}"
            )
        else:
            self._specifications[specification.name] = specification

    def include(self, other: "FigureRegistry") -> None:
        for specification in other:
            self.add(specification)

    def names(self) -> tuple[str, ...]:
        return tuple(self._specifications)

    def select(self, wanted: Collection[str]) -> list[FigureSpecification]:
        if wanted:
            missing = sorted(set(wanted) - set(self._specifications))
            if missing:
                raise KeyError(f"unknown figures: {', '.join(missing)}")
            else:
                return [
                    specification
                    for specification in self._specifications.values()
                    if specification.name in wanted
                ]
        else:
            return list(self._specifications.values())

    def __iter__(self) -> Iterator[FigureSpecification]:
        return iter(self._specifications.values())

    def __len__(self) -> int:
        return len(self._specifications)
