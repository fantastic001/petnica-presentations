from __future__ import annotations

import logging
from pathlib import Path

from .output import FigureWriter
from .registry import FigureRegistry
from .runner import FigureRunner
from .settings import DEFAULT_ENVIRONMENT_PREFIX, RenderSettings
from .style import resolve_style_profile

log = logging.getLogger(__name__)


def render_registry(
    registry: FigureRegistry,
    default_directory: Path,
    prefix: str = DEFAULT_ENVIRONMENT_PREFIX,
    default_seed: int = 42,
) -> int:
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    settings = RenderSettings.from_environment(
        default_directory, prefix, default_seed
    )
    profile = resolve_style_profile(settings.style_name)
    profile.apply()
    writer = FigureWriter(
        directory=settings.output_directory,
        output_format=settings.output_format,
        dpi=settings.dpi,
    )
    writer.prepare()
    runner = FigureRunner(registry, writer, profile.palette, settings)
    report = runner.render()
    return 1 if report.failed else 0
