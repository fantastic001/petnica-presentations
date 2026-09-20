from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Palette:
    blue: str
    orange: str
    aqua: str
    yellow: str
    magenta: str
    green: str
    violet: str
    red: str
    ink: str
    muted_ink: str
    grid: str
    surface: str

    def series(self) -> tuple[str, ...]:
        return (
            self.blue,
            self.orange,
            self.aqua,
            self.yellow,
            self.magenta,
            self.green,
            self.violet,
            self.red,
        )

    def series_color(self, index: int) -> str:
        colors = self.series()
        if 0 <= index < len(colors):
            return colors[index]
        else:
            raise IndexError(
                f"palette has {len(colors)} series colors, asked for {index}"
            )


LIGHT_PALETTE = Palette(
    blue="#2a78d6",
    orange="#eb6834",
    aqua="#1baf7a",
    yellow="#eda100",
    magenta="#e87ba4",
    green="#008300",
    violet="#4a3aa7",
    red="#e34948",
    ink="#0b0b0b",
    muted_ink="#52514e",
    grid="#e4e3df",
    surface="#fcfcfb",
)

DARK_PALETTE = Palette(
    blue="#3987e5",
    orange="#d95926",
    aqua="#199e70",
    yellow="#c98500",
    magenta="#d55181",
    green="#008300",
    violet="#9085e9",
    red="#e66767",
    ink="#ffffff",
    muted_ink="#c3c2b7",
    grid="#3a3a38",
    surface="#1a1a19",
)

PALETTES: dict[str, Palette] = {
    "light": LIGHT_PALETTE,
    "dark": DARK_PALETTE,
}


def resolve_palette(name: str) -> Palette:
    if name in PALETTES:
        return PALETTES[name]
    else:
        known = ", ".join(sorted(PALETTES))
        raise KeyError(f"unknown palette {name!r}, available: {known}")
