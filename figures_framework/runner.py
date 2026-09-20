from __future__ import annotations

import logging
import random
from dataclasses import dataclass, field

import numpy as np

from .context import FigureContext
from .output import FigureSink
from .palette import Palette
from .registry import FigureRegistry, FigureSpecification
from .settings import RenderMode, RenderSettings

log = logging.getLogger(__name__)


@dataclass(frozen=True)
class RenderReport:
    rendered: tuple[str, ...] = ()
    skipped: tuple[str, ...] = ()
    failed: tuple[str, ...] = ()

    def summary(self) -> str:
        return (
            f"{len(self.rendered)} rendered, {len(self.skipped)} skipped, "
            f"{len(self.failed)} failed"
        )


@dataclass
class RenderOutcome:
    rendered: list[str] = field(default_factory=list)
    skipped: list[str] = field(default_factory=list)
    failed: list[str] = field(default_factory=list)

    def report(self) -> RenderReport:
        return RenderReport(
            rendered=tuple(self.rendered),
            skipped=tuple(self.skipped),
            failed=tuple(self.failed),
        )


class FigureRunner:
    def __init__(
        self,
        registry: FigureRegistry,
        sink: FigureSink,
        palette: Palette,
        settings: RenderSettings,
    ) -> None:
        self.registry = registry
        self.sink = sink
        self.palette = palette
        self.settings = settings

    def render(self) -> RenderReport:
        log.info("rendering figures from %s", self.registry.name)
        outcome = RenderOutcome()
        for specification in self.registry.select(self.settings.selected):
            self._render_one(specification, outcome)
        report = outcome.report()
        log.info("done: %s", report.summary())
        return report

    def _render_one(
        self, specification: FigureSpecification, outcome: RenderOutcome
    ) -> None:
        if self._is_already_rendered(specification):
            log.info("skipping %s, output exists", specification.name)
            outcome.skipped.append(specification.name)
        else:
            try:
                figure = specification.render(self._build_context())
                self.sink.write(figure, specification.name)
                outcome.rendered.append(specification.name)
            except Exception:
                log.exception("figure %s failed", specification.name)
                outcome.failed.append(specification.name)

    def _is_already_rendered(self, specification: FigureSpecification) -> bool:
        match self.settings.mode:
            case RenderMode.REBUILD:
                return False
            case RenderMode.RESUME:
                return self.sink.path_for(specification.name).exists()

    def _build_context(self) -> FigureContext:
        random.seed(self.settings.seed)
        return FigureContext(
            palette=self.palette,
            random=np.random.default_rng(self.settings.seed),
            seed=self.settings.seed,
        )
