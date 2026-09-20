from __future__ import annotations

import os
from dataclasses import dataclass
from enum import Enum
from pathlib import Path

from .output import DEFAULT_DPI, OutputFormat, resolve_output_format

DEFAULT_ENVIRONMENT_PREFIX = "FIGURES_"


class RenderMode(Enum):
    REBUILD = "rebuild"
    RESUME = "resume"


def resolve_render_mode(name: str) -> RenderMode:
    for candidate in RenderMode:
        if candidate.value == name.lower():
            return candidate
        else:
            continue
    known = ", ".join(item.value for item in RenderMode)
    raise ValueError(f"unknown mode {name!r}, available: {known}")


def environment_text(name: str, fallback: str) -> str:
    return os.environ.get(name, fallback)


def environment_integer(name: str, fallback: int) -> int:
    raw = os.environ.get(name)
    if raw is None:
        return fallback
    else:
        try:
            return int(raw)
        except ValueError as error:
            message = f"{name} must be an integer, got {raw!r}"
            raise ValueError(message) from error


@dataclass(frozen=True)
class RenderSettings:
    output_directory: Path
    output_format: OutputFormat = OutputFormat.SVG
    dpi: int = DEFAULT_DPI
    seed: int = 42
    selected: tuple[str, ...] = ()
    style_name: str = "light"
    mode: RenderMode = RenderMode.REBUILD

    @classmethod
    def from_environment(
        cls,
        default_directory: Path,
        prefix: str = DEFAULT_ENVIRONMENT_PREFIX,
        default_seed: int = 42,
    ) -> "RenderSettings":
        selection = environment_text(f"{prefix}ONLY", "")
        return cls(
            output_directory=Path(
                environment_text(f"{prefix}OUTPUT_DIR", str(default_directory))
            ),
            output_format=resolve_output_format(
                environment_text(f"{prefix}FORMAT", OutputFormat.SVG.value)
            ),
            dpi=environment_integer(f"{prefix}DPI", DEFAULT_DPI),
            seed=environment_integer(f"{prefix}SEED", default_seed),
            selected=tuple(name for name in selection.split(",") if name),
            style_name=environment_text(f"{prefix}STYLE", "light"),
            mode=resolve_render_mode(
                environment_text(f"{prefix}MODE", RenderMode.REBUILD.value)
            ),
        )
