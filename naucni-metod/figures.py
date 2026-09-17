from __future__ import annotations

import logging
import math
import os
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import networkx as nx
import numpy as np
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch

OUTPUT_DIRECTORY = Path(
    os.environ.get("FIGURES_OUTPUT_DIR", Path(__file__).parent / "img")
)
OUTPUT_FORMAT = os.environ.get("FIGURES_FORMAT", "svg")
RANDOM_SEED = int(os.environ.get("FIGURES_SEED", "42"))
SELECTED_FIGURES = os.environ.get("FIGURES_ONLY", "")
QUICKSORT_REPETITIONS = int(os.environ.get("QUICKSORT_REPETITIONS", "30"))
ER_REPETITIONS = int(os.environ.get("ER_REPETITIONS", "20"))

BLUE = "#2a78d6"
ORANGE = "#eb6834"
AQUA = "#1baf7a"
YELLOW = "#eda100"
MAGENTA = "#e87ba4"
GREEN = "#008300"
VIOLET = "#4a3aa7"
RED = "#e34948"
INK = "#0b0b0b"
MUTED_INK = "#52514e"
GRID = "#e4e3df"
SURFACE = "#fcfcfb"
FIGURE_DPI = int(os.environ.get("FIGURES_DPI", "150"))
FIGURE_SIZE_WIDE = (10, 4.6)
FIGURE_SIZE_SQUARE = (6, 6)
FIGURE_SIZE_DIAGRAM = (10, 5)

log = logging.getLogger("figures")


def configure_style() -> None:
    plt.rcParams.update(
        {
            "figure.facecolor": SURFACE,
            "axes.facecolor": SURFACE,
            "savefig.facecolor": SURFACE,
            "axes.edgecolor": MUTED_INK,
            "axes.labelcolor": INK,
            "axes.titlecolor": INK,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.grid": True,
            "grid.color": GRID,
            "grid.linewidth": 0.8,
            "xtick.color": MUTED_INK,
            "ytick.color": MUTED_INK,
            "font.size": 16,
            "axes.titlesize": 18,
            "legend.fontsize": 15,
            "legend.frameon": False,
            "lines.linewidth": 2.2,
        }
    )


def save_figure(figure: plt.Figure, name: str) -> None:
    path = OUTPUT_DIRECTORY / f"{name}.{OUTPUT_FORMAT}"
    figure.tight_layout()
    figure.savefig(path, format=OUTPUT_FORMAT, dpi=FIGURE_DPI)
    plt.close(figure)
    log.info("saved %s", path)


def create_blank_canvas(size: tuple[float, float]) -> tuple:
    figure, axes = plt.subplots(figsize=size)
    axes.set_axis_off()
    axes.grid(False)
    return figure, axes


def draw_box(axes, center, text, color, width=2.2, height=0.9) -> None:
    x, y = center
    axes.add_patch(
        FancyBboxPatch(
            (x - width / 2, y - height / 2),
            width,
            height,
            boxstyle="round,pad=0.05,rounding_size=0.18",
            facecolor=color,
            edgecolor="none",
        )
    )
    axes.text(
        x, y, text, ha="center", va="center", color="white",
        fontsize=15, fontweight="bold",
    )


def draw_arrow(axes, start, end, color=MUTED_INK, curve=0.0) -> None:
    axes.add_patch(
        FancyArrowPatch(
            start,
            end,
            arrowstyle="-|>",
            mutation_scale=22,
            color=color,
            linewidth=2,
            connectionstyle=f"arc3,rad={curve}",
        )
    )


def point_between(start, end, fraction):
    return (
        start[0] + (end[0] - start[0]) * fraction,
        start[1] + (end[1] - start[1]) * fraction,
    )


def figure_scientific_cycle() -> None:
    steps = [
        ("Posmatranje", BLUE),
        ("Pitanje", VIOLET),
        ("Hipoteza", ORANGE),
        ("Dizajn\neksperimenta", AQUA),
        ("Eksperiment", GREEN),
        ("Analiza", YELLOW),
        ("Zaključak\n→ teorija", RED),
    ]
    figure, axes = create_blank_canvas((9, 8.4))
    radius = 3.9
    angles = [
        math.pi / 2 - 2 * math.pi * k / len(steps)
        for k in range(len(steps))
    ]
    centers = [(radius * math.cos(a), radius * math.sin(a)) for a in angles]
    for (label, color), center in zip(steps, centers):
        draw_box(axes, center, label, color, width=2.5, height=1.1)
    for k, start in enumerate(centers):
        end = centers[(k + 1) % len(centers)]
        draw_arrow(
            axes,
            point_between(start, end, 0.33),
            point_between(start, end, 0.67),
        )
    axes.text(
        0, 0, "nove\npredikcije", ha="center", va="center",
        fontsize=20, color=MUTED_INK, style="italic",
    )
    axes.set_xlim(-5.4, 5.4)
    axes.set_ylim(-4.6, 4.8)
    axes.set_aspect("equal")
    save_figure(figure, "scientific_cycle")


def figure_induction_deduction() -> None:
    figure, axes = create_blank_canvas(FIGURE_SIZE_DIAGRAM)
    draw_box(axes, (0, 3), "Teorija", RED, width=2.6)
    draw_box(axes, (-3.2, 1.2), "Hipoteza", ORANGE, width=2.6)
    draw_box(axes, (3.2, 1.2), "Uopštavanje", VIOLET, width=2.6)
    draw_box(axes, (-3.2, -0.8), "Predikcija", AQUA, width=2.6)
    draw_box(axes, (3.2, -0.8), "Obrasci", YELLOW, width=2.6)
    draw_box(axes, (0, -2.4), "Podaci / merenja", BLUE, width=3.4)
    draw_arrow(axes, (-1.4, 2.7), (-2.6, 1.7))
    draw_arrow(axes, (-3.2, 0.7), (-3.2, -0.3))
    draw_arrow(axes, (-2.6, -1.3), (-1.6, -2.0))
    draw_arrow(axes, (1.6, -2.0), (2.6, -1.3))
    draw_arrow(axes, (3.2, -0.3), (3.2, 0.7))
    draw_arrow(axes, (2.6, 1.7), (1.4, 2.7))
    axes.text(-4.9, 0.2, "DEDUKCIJA", rotation=90, ha="center",
              va="center", color=ORANGE, fontsize=16, fontweight="bold")
    axes.text(4.9, 0.2, "INDUKCIJA", rotation=90, ha="center",
              va="center", color=VIOLET, fontsize=16, fontweight="bold")
    axes.set_xlim(-5.5, 5.5)
    axes.set_ylim(-3.2, 3.7)
    save_figure(figure, "induction_deduction")


def figure_experiment_variables() -> None:
    figure, axes = create_blank_canvas(FIGURE_SIZE_DIAGRAM)
    draw_box(axes, (-4, 0), "Nezavisna\npromenljiva  $x$", BLUE, 2.8, 1.3)
    draw_box(axes, (0, 0), "Sistem", MUTED_INK, 2.4, 1.6)
    draw_box(axes, (4, 0), "Zavisna\npromenljiva  $y$", ORANGE, 2.8, 1.3)
    draw_box(axes, (0, 2.6), "Kontrolne promenljive  (fiksne)", AQUA, 5.2, 0.9)
    draw_box(axes, (0, -2.6), "Šum  $\\varepsilon$  (ne kontrolišemo)",
             RED, 5.2, 0.9)
    draw_arrow(axes, (-2.55, 0), (-1.3, 0))
    draw_arrow(axes, (1.3, 0), (2.55, 0))
    draw_arrow(axes, (0, 2.1), (0, 0.9))
    draw_arrow(axes, (0, -2.1), (0, -0.9))
    axes.text(0, -3.55, "$y = f(x) + \\varepsilon$", ha="center",
              fontsize=22, color=INK)
    axes.set_xlim(-5.8, 5.8)
    axes.set_ylim(-4, 3.3)
    save_figure(figure, "experiment_variables")


def figure_randomized_groups() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    figure, axes = create_blank_canvas(FIGURE_SIZE_DIAGRAM)
    population = generator.uniform([-5.3, -2], [-2.7, 2], size=(24, 2))
    colors = [MUTED_INK] * len(population)
    axes.scatter(population[:, 0], population[:, 1], s=160, c=colors)
    axes.text(-4, 2.6, "Uzorak", ha="center", fontsize=16, color=INK)
    draw_box(axes, (0, 0), "slučajna\npodela", VIOLET, 2.2, 1.3)
    draw_arrow(axes, (-2.5, 0), (-1.2, 0))
    draw_arrow(axes, (1.2, 0.4), (2.4, 1.6))
    draw_arrow(axes, (1.2, -0.4), (2.4, -1.6))
    treated = generator.uniform([2.6, 1.0], [5.2, 2.8], size=(12, 2))
    control = generator.uniform([2.6, -2.8], [5.2, -1.0], size=(12, 2))
    axes.scatter(treated[:, 0], treated[:, 1], s=160, c=ORANGE)
    axes.scatter(control[:, 0], control[:, 1], s=160, c=BLUE)
    axes.text(3.9, 3.2, "Tretman", ha="center", color=ORANGE, fontsize=16)
    axes.text(3.9, -3.5, "Kontrola", ha="center", color=BLUE, fontsize=16)
    axes.set_xlim(-6, 6)
    axes.set_ylim(-4, 3.8)
    save_figure(figure, "randomized_groups")


def figure_random_variable_map() -> None:
    figure, axes = create_blank_canvas(FIGURE_SIZE_DIAGRAM)
    axes.add_patch(
        Circle((-3, 0), 2.2, facecolor="#eef3fb", edgecolor=BLUE, lw=2)
    )
    axes.text(-3, 2.5, "$\\Omega$ — ishodi", ha="center", fontsize=18)
    outcomes = ["⚀", "⚁", "⚂", "⚃", "⚄", "⚅"]
    outcome_positions = [
        (-3.9, 1.1), (-2.2, 1.2), (-3.9, 0), (-2.1, 0),
        (-3.8, -1.2), (-2.3, -1.2),
    ]
    axes.plot([1, 6], [0, 0], color=INK, lw=2)
    for value in range(1, 7):
        axes.plot([value, value], [-0.12, 0.12], color=INK, lw=2)
        axes.text(value, -0.55, str(value), ha="center", fontsize=16)
    for index, (symbol, position) in enumerate(
        zip(outcomes, outcome_positions)
    ):
        axes.text(*position, symbol, ha="center", va="center", fontsize=34,
                  family="DejaVu Sans")
        draw_arrow(
            axes,
            (position[0] + 0.35, position[1]),
            (index + 1, 0.2),
            color=BLUE if index % 2 else ORANGE,
            curve=-0.2,
        )
    axes.text(3.5, -1.5, "$\\mathbb{R}$", ha="center", fontsize=22)
    axes.text(0.3, 2.3, "$X:\\ \\Omega \\to \\mathbb{R}$", ha="center",
              fontsize=24)
    axes.set_xlim(-5.6, 6.6)
    axes.set_ylim(-2.6, 3.1)
    save_figure(figure, "random_variable_map")


def figure_uniform() -> None:
    figure, (left, right) = plt.subplots(1, 2, figsize=FIGURE_SIZE_WIDE)
    faces = np.arange(1, 7)
    left.bar(faces, np.full(6, 1 / 6), color=BLUE, width=0.7)
    left.set_title("Diskretna: kocka")
    left.set_xlabel("$k$")
    left.set_ylabel("$P(X=k)$")
    left.set_ylim(0, 0.3)
    x = np.linspace(-0.5, 3.5, 800)
    density = np.where((x >= 1) & (x <= 3), 0.5, 0.0)
    right.fill_between(x, density, color=ORANGE, alpha=0.25)
    right.plot(x, density, color=ORANGE)
    right.set_title("Neprekidna: $U(a,b)$")
    right.set_xticks([1, 3], ["$a$", "$b$"])
    right.set_yticks([0.5], ["$\\frac{1}{b-a}$"])
    right.set_ylim(0, 0.8)
    save_figure(figure, "uniform")


def figure_uniform_samples() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    sample_sizes = [10, 100, 10000]
    figure, axes_row = plt.subplots(1, 3, figsize=FIGURE_SIZE_WIDE,
                                    sharey=True)
    for axes, size in zip(axes_row, sample_sizes):
        rolls = generator.integers(1, 7, size=size)
        counts = np.bincount(rolls, minlength=7)[1:] / size
        axes.bar(np.arange(1, 7), counts, color=BLUE, width=0.7)
        axes.axhline(1 / 6, color=ORANGE, ls="--")
        axes.set_title(f"$n = {size}$")
        axes.set_xticks(range(1, 7))
    axes_row[0].set_ylabel("relativna frekvencija")
    save_figure(figure, "uniform_samples")


def figure_bernoulli() -> None:
    figure, axes = plt.subplots(figsize=(6, 4.4))
    probability = 0.3
    axes.bar([0, 1], [1 - probability, probability], color=[BLUE, ORANGE],
             width=0.55)
    axes.set_xticks([0, 1], ["0\n(neuspeh)", "1\n(uspeh)"])
    axes.set_yticks([probability, 1 - probability], ["$p$", "$1-p$"])
    axes.set_ylim(0, 1)
    axes.set_title("$X \\sim \\mathrm{Bernoulli}(p)$")
    save_figure(figure, "bernoulli")


def binomial_pmf(trials: int, probability: float) -> np.ndarray:
    return np.array(
        [
            math.comb(trials, k)
            * probability ** k
            * (1 - probability) ** (trials - k)
            for k in range(trials + 1)
        ]
    )


def figure_binomial() -> None:
    trials = 20
    parameters = [(0.2, BLUE), (0.5, ORANGE), (0.8, AQUA)]
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    k = np.arange(trials + 1)
    width = 0.28
    for offset, (probability, color) in zip([-1, 0, 1], parameters):
        axes.bar(k + offset * width, binomial_pmf(trials, probability),
                 width=width, color=color, label=f"$p={probability}$")
    axes.set_xlabel("$k$ — broj uspeha od $n=20$")
    axes.set_ylabel("$P(X=k)$")
    axes.legend()
    save_figure(figure, "binomial")


def figure_galton_board() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    rows = 12
    balls = 5000
    positions = generator.binomial(rows, 0.5, size=balls)
    figure, (board, histogram) = plt.subplots(
        1, 2, figsize=FIGURE_SIZE_WIDE, gridspec_kw={"width_ratios": [1, 1.3]}
    )
    board.set_axis_off()
    board.grid(False)
    for row in range(rows):
        for pin in range(row + 1):
            board.scatter(pin - row / 2, -row, s=18, color=MUTED_INK)
    path_x = 0.0
    for row in range(rows):
        step = generator.choice([-0.5, 0.5])
        board.plot([path_x, path_x + step], [-row, -row - 1], color=ORANGE,
                   lw=2.5)
        path_x += step
    board.set_title("Galtonova tabla")
    counts = np.bincount(positions, minlength=rows + 1) / balls
    histogram.bar(np.arange(rows + 1), counts, color=BLUE, width=0.8,
                  label="simulacija")
    histogram.plot(np.arange(rows + 1), binomial_pmf(rows, 0.5), "o",
                   color=ORANGE, ms=8, label="$B(12, 1/2)$")
    histogram.set_xlabel("pregrada $k$")
    histogram.legend()
    save_figure(figure, "galton_board")


def normal_pdf(x: np.ndarray, mean: float, deviation: float) -> np.ndarray:
    scale = 1 / (deviation * math.sqrt(2 * math.pi))
    return scale * np.exp(-0.5 * ((x - mean) / deviation) ** 2)


def figure_normal_rule() -> None:
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    x = np.linspace(-4, 4, 1000)
    y = normal_pdf(x, 0, 1)
    bands = [(3, "#dbe8f8", "99.7%"), (2, "#9fc2ec", "95%"),
             (1, BLUE, "68%")]
    for width, color, label in bands:
        mask = np.abs(x) <= width
        axes.fill_between(x[mask], y[mask], color=color)
    axes.plot(x, y, color=INK)
    for width, _, label in bands:
        level = -0.045 * width
        axes.annotate(
            "", xy=(-width, level), xytext=(width, level),
            arrowprops={"arrowstyle": "<->", "color": INK},
        )
        axes.text(width + 0.12, level, label, va="center", fontsize=13,
                  color=INK)
    axes.set_ylim(-0.16, 0.43)
    axes.spines["bottom"].set_visible(False)
    axes.spines["left"].set_visible(False)
    axes.set_xticks(range(-3, 4), [
        "$\\mu-3\\sigma$", "$\\mu-2\\sigma$", "$\\mu-\\sigma$", "$\\mu$",
        "$\\mu+\\sigma$", "$\\mu+2\\sigma$", "$\\mu+3\\sigma$",
    ])
    axes.set_yticks([])
    save_figure(figure, "normal_rule")


def figure_normal_parameters() -> None:
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    x = np.linspace(-6, 8, 1000)
    parameters = [(0, 1, BLUE), (0, 2, ORANGE), (3, 0.6, AQUA)]
    for mean, deviation, color in parameters:
        axes.plot(x, normal_pdf(x, mean, deviation), color=color,
                  label=f"$\\mu={mean},\\ \\sigma={deviation}$")
    axes.set_xlabel("$x$")
    axes.set_ylabel("$f(x)$")
    axes.legend()
    save_figure(figure, "normal_parameters")


def figure_white_noise() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    samples = 300
    noise = generator.normal(0, 1, size=samples)
    figure, (series, histogram) = plt.subplots(
        1, 2, figsize=FIGURE_SIZE_WIDE, gridspec_kw={"width_ratios": [2.2, 1]},
        sharey=True,
    )
    series.plot(noise, color=BLUE, lw=1.2)
    series.set_xlabel("vreme $t$")
    series.set_ylabel("$\\varepsilon_t$")
    series.set_title("$\\varepsilon_t \\sim N(0, \\sigma^2)$, nezavisni")
    bins = np.linspace(-4, 4, 25)
    histogram.hist(noise, bins=bins, orientation="horizontal", color=BLUE,
                   density=True, alpha=0.6)
    y = np.linspace(-4, 4, 200)
    histogram.plot(normal_pdf(y, 0, 1), y, color=ORANGE)
    histogram.set_title("raspodela")
    save_figure(figure, "white_noise")


def figure_signal_plus_noise() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    t = np.linspace(0, 10, 120)
    signal = 2 * np.sin(t * 0.8) + 0.3 * t
    measured = signal + generator.normal(0, 0.8, size=t.size)
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    axes.scatter(t, measured, s=22, color=BLUE, label="merenje $y$")
    axes.plot(t, signal, color=ORANGE, lw=3, label="zakon $f(t)$")
    axes.set_xlabel("$t$")
    axes.legend()
    axes.set_title("$y = f(t) + \\varepsilon$")
    save_figure(figure, "signal_plus_noise")


def figure_noise_autocorrelation() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    samples = 2000
    white = generator.normal(size=samples)
    walk = np.cumsum(generator.normal(size=samples))
    figure, (white_axes, walk_axes) = plt.subplots(1, 2,
                                                   figsize=FIGURE_SIZE_WIDE)
    white_axes.scatter(white[:-1], white[1:], s=5, color=BLUE, alpha=0.5,
                       rasterized=True)
    white_axes.set_title("beli šum: $\\varepsilon_t$ vs $\\varepsilon_{t+1}$")
    walk_axes.scatter(walk[:-1], walk[1:], s=5, color=ORANGE, alpha=0.5,
                      rasterized=True)
    walk_axes.set_title("nije beli šum: $x_t$ vs $x_{t+1}$")
    for axes in (white_axes, walk_axes):
        axes.set_aspect("equal", adjustable="datalim")
    save_figure(figure, "noise_autocorrelation")


def figure_central_limit() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    sample_sizes = [1, 2, 5, 30]
    repetitions = 20000
    figure, axes_row = plt.subplots(1, 4, figsize=(12, 3.8), sharey=False)
    for axes, size in zip(axes_row, sample_sizes):
        means = generator.exponential(1, size=(repetitions, size)).mean(1)
        axes.hist(means, bins=60, density=True, color=BLUE, alpha=0.75)
        x = np.linspace(0, 4, 400)
        if size >= 5:
            axes.plot(x, normal_pdf(x, 1, 1 / math.sqrt(size)),
                      color=ORANGE)
        else:
            axes.plot([], [])
        axes.set_xlim(0, 4)
        axes.set_yticks([])
        axes.set_title(f"$n = {size}$")
    axes_row[0].set_xlabel("$\\bar{X}_n$, $X_i \\sim \\mathrm{Exp}(1)$")
    save_figure(figure, "central_limit")


def figure_dice_sums() -> None:
    figure, axes_row = plt.subplots(1, 4, figsize=(12, 3.8))
    distribution = np.full(6, 1 / 6)
    single_die = np.full(6, 1 / 6)
    for index, axes in enumerate(axes_row):
        dice = index + 1 if index < 3 else 10
        current = single_die
        for _ in range(dice - 1):
            current = np.convolve(current, distribution)
        support = np.arange(dice, 6 * dice + 1)
        axes.bar(support, current, color=BLUE, width=0.8)
        axes.set_title(f"zbir {dice} kock{'a' if dice > 1 else 'e'}")
        axes.set_yticks([])
    save_figure(figure, "dice_sums")


def figure_standard_error() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    sample_sizes = [2, 5, 10, 20, 50, 100, 200, 500]
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    for size in sample_sizes:
        means = generator.normal(10, 2, size=(40, size)).mean(1)
        jitter = generator.uniform(-0.03, 0.03, size=means.size)
        axes.scatter(size * (1 + jitter), means, s=16, color=BLUE,
                     alpha=0.7)
    n = np.logspace(math.log10(2), math.log10(500), 200)
    axes.plot(n, 10 + 2 * 2 / np.sqrt(n), color=ORANGE,
              label="$\\mu \\pm 2\\sigma/\\sqrt{n}$")
    axes.plot(n, 10 - 2 * 2 / np.sqrt(n), color=ORANGE)
    axes.set_xscale("log")
    axes.set_xlabel("veličina uzorka $n$")
    axes.set_ylabel("$\\bar{x}$")
    axes.legend()
    save_figure(figure, "standard_error")


def figure_confidence_intervals() -> None:
    generator = np.random.default_rng(RANDOM_SEED + 3)
    true_mean, deviation, size, intervals = 10, 2, 25, 30
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    half_width = 1.96 * deviation / math.sqrt(size)
    for index in range(intervals):
        mean = generator.normal(true_mean, deviation, size=size).mean()
        misses = abs(mean - true_mean) > half_width
        color = RED if misses else BLUE
        axes.plot([index, index], [mean - half_width, mean + half_width],
                  color=color, lw=3)
        axes.scatter(index, mean, color=color, s=30, zorder=3)
    axes.axhline(true_mean, color=INK, ls="--", label="pravo $\\mu$")
    axes.set_xlabel("ponovljeni eksperiment")
    axes.set_ylabel("95% interval")
    axes.legend(loc="upper right")
    save_figure(figure, "confidence_intervals")


def figure_p_value() -> None:
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    x = np.linspace(-4, 4, 1000)
    y = normal_pdf(x, 0, 1)
    observed = 2.2
    axes.plot(x, y, color=INK)
    axes.fill_between(x[x >= observed], y[x >= observed], color=ORANGE)
    axes.fill_between(x[x <= -observed], y[x <= -observed], color=ORANGE)
    axes.axvline(observed, color=BLUE, lw=2.5)
    axes.text(observed + 0.1, 0.3, "izmereno $t$", color=BLUE, fontsize=15)
    axes.annotate("p-vrednost", xy=(2.6, 0.012), xytext=(2.6, 0.15),
                  ha="center", fontsize=15,
                  arrowprops={"arrowstyle": "->", "color": INK})
    axes.text(-3.9, 0.35, "raspodela statistike\nako važi $H_0$",
              fontsize=14, color=MUTED_INK)
    axes.set_yticks([])
    save_figure(figure, "p_value")


def figure_error_types() -> None:
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    x = np.linspace(-4, 7, 1200)
    null = normal_pdf(x, 0, 1)
    alternative = normal_pdf(x, 3, 1)
    threshold = 1.645
    axes.plot(x, null, color=BLUE, label="$H_0$ tačna")
    axes.plot(x, alternative, color=ORANGE, label="$H_1$ tačna")
    axes.fill_between(x[x >= threshold], null[x >= threshold], color=BLUE,
                      alpha=0.45)
    axes.fill_between(x[x <= threshold], alternative[x <= threshold],
                      color=ORANGE, alpha=0.45)
    axes.axvline(threshold, color=INK, ls="--")
    axes.text(2.1, 0.03, "$\\alpha$", fontsize=20, color=BLUE)
    axes.text(0.9, 0.03, "$\\beta$", fontsize=20, color=ORANGE)
    axes.text(threshold + 0.1, 0.42, "prag odluke", fontsize=13)
    axes.set_yticks([])
    axes.legend(loc="upper left")
    save_figure(figure, "error_types")


def figure_accuracy_precision() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    cases = [
        ("tačno i precizno", 0.0, 0.15),
        ("netačno, precizno", 0.9, 0.15),
        ("tačno, neprecizno", 0.0, 0.6),
        ("netačno i neprecizno", 0.9, 0.6),
    ]
    figure, axes_row = plt.subplots(1, 4, figsize=(12, 3.6))
    for axes, (title, bias, spread) in zip(axes_row, cases):
        axes.set_axis_off()
        axes.grid(False)
        for ring, color in zip([2, 1.4, 0.8, 0.25],
                               ["#eef3fb", "#cfdff4", "#9fc2ec", BLUE]):
            axes.add_patch(Circle((0, 0), ring, color=color))
        shots = generator.normal([bias, bias * 0.6], spread, size=(12, 2))
        axes.scatter(shots[:, 0], shots[:, 1], color=ORANGE, s=40,
                     edgecolor="white", zorder=3)
        axes.set_xlim(-2.1, 2.1)
        axes.set_ylim(-2.1, 2.1)
        axes.set_aspect("equal")
        axes.set_title(title, fontsize=14)
    save_figure(figure, "accuracy_precision")


def figure_monte_carlo_pi() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    points = generator.uniform(0, 1, size=(3000, 2))
    inside = (points ** 2).sum(1) <= 1
    figure, (scatter, convergence) = plt.subplots(
        1, 2, figsize=FIGURE_SIZE_WIDE, gridspec_kw={"width_ratios": [1, 1.5]}
    )
    scatter.scatter(*points[inside].T, s=3, color=BLUE, rasterized=True)
    scatter.scatter(*points[~inside].T, s=3, color=ORANGE, rasterized=True)
    scatter.set_aspect("equal")
    scatter.set_title("$\\pi \\approx 4 \\cdot$ unutra / ukupno")
    many = generator.uniform(0, 1, size=(200000, 2))
    hits = np.cumsum((many ** 2).sum(1) <= 1)
    n = np.arange(1, many.shape[0] + 1)
    estimate = 4 * hits / n
    visible = np.unique(np.logspace(0, math.log10(n.size), 1500).astype(int))
    convergence.plot(n[visible - 1], estimate[visible - 1], color=BLUE,
                     lw=1.4, label="procena")
    convergence.axhline(math.pi, color=INK, ls="--", label="$\\pi$")
    band = 1.96 * 4 * math.sqrt(math.pi / 4 * (1 - math.pi / 4)) / np.sqrt(n)
    convergence.fill_between(n[visible - 1], math.pi - band[visible - 1],
                             math.pi + band[visible - 1],
                             color=ORANGE, alpha=0.2, label="$\\pm 2\\,SE$")
    convergence.set_xscale("log")
    convergence.set_ylim(2.6, 3.7)
    convergence.set_xlabel("broj tačaka $n$")
    convergence.legend()
    save_figure(figure, "monte_carlo_pi")


class ComparisonCountingQuicksort:
    def __init__(self, pivot_strategy: Callable[[list[int]], int]) -> None:
        self.pivot_strategy = pivot_strategy

    def count_comparisons(self, values: list[int]) -> int:
        comparisons = 0
        pending = [values]
        while pending:
            current = pending.pop()
            if len(current) <= 1:
                continue
            pivot = current[self.pivot_strategy(current)]
            comparisons += len(current) - 1
            pending.append([v for v in current if v < pivot])
            pending.append([v for v in current if v > pivot])
        return comparisons


def choose_random_pivot(values: list[int]) -> int:
    return random.randrange(len(values))


def choose_first_pivot(values: list[int]) -> int:
    return 0


def expected_quicksort_comparisons(size: int) -> float:
    harmonic = sum(1 / k for k in range(1, size + 1))
    return 2 * (size + 1) * harmonic - 4 * size


def measure_quicksort(sizes, strategy, input_builder, repetitions):
    sorter = ComparisonCountingQuicksort(strategy)
    return np.array(
        [
            [
                sorter.count_comparisons(input_builder(size))
                for _ in range(repetitions)
            ]
            for size in sizes
        ],
        dtype=float,
    )


def build_shuffled_input(size: int) -> list[int]:
    values = list(range(size))
    random.shuffle(values)
    return values


def build_sorted_input(size: int) -> list[int]:
    return list(range(size))


QUICKSORT_SIZES = [100, 200, 500, 1000, 2000, 5000, 10000, 20000]


def figure_quicksort_mean() -> None:
    measurements = measure_quicksort(
        QUICKSORT_SIZES, choose_random_pivot, build_shuffled_input,
        QUICKSORT_REPETITIONS,
    )
    sizes = np.array(QUICKSORT_SIZES)
    figure, (absolute, ratio) = plt.subplots(1, 2, figsize=FIGURE_SIZE_WIDE)
    means = measurements.mean(1)
    deviations = measurements.std(1, ddof=1)
    absolute.errorbar(sizes, means, yerr=2 * deviations, fmt="o",
                      color=BLUE, ms=8, capsize=4, label="merenje")
    theory = [expected_quicksort_comparisons(int(n)) for n in sizes]
    absolute.plot(sizes, theory, color=ORANGE, label="$E[C_n]$ (teorija)")
    absolute.set_xlabel("$n$")
    absolute.set_ylabel("broj poređenja $C_n$")
    absolute.legend()
    normalized = measurements / (sizes * np.log(sizes))[:, None]
    ratio.errorbar(sizes, normalized.mean(1),
                   yerr=2 * normalized.std(1, ddof=1), fmt="o", color=BLUE,
                   ms=8, capsize=4)
    ratio.plot(sizes, np.array(theory) / (sizes * np.log(sizes)),
               color=ORANGE)
    ratio.axhline(2, color=INK, ls="--")
    ratio.set_xscale("log")
    ratio.set_xlabel("$n$")
    ratio.set_ylabel("$C_n / (n \\ln n)$")
    save_figure(figure, "quicksort_mean")


def figure_quicksort_distribution() -> None:
    size, repetitions = 2000, 2000
    measurements = measure_quicksort(
        [size], choose_random_pivot, build_shuffled_input, repetitions
    )[0]
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    axes.hist(measurements, bins=45, color=BLUE, alpha=0.75, density=True)
    axes.axvline(expected_quicksort_comparisons(size), color=ORANGE, lw=3,
                 label="$E[C_n]$ teorija")
    axes.set_xlabel(f"broj poređenja, $n = {size}$, {repetitions} ponavljanja")
    axes.set_yticks([])
    axes.legend()
    save_figure(figure, "quicksort_distribution")


def figure_quicksort_loglog() -> None:
    sizes = [100, 200, 400, 800, 1600, 3200]
    random_pivot = measure_quicksort(sizes, choose_random_pivot,
                                     build_sorted_input, 5).mean(1)
    first_pivot = measure_quicksort(sizes, choose_first_pivot,
                                    build_sorted_input, 1).mean(1)
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    axes.loglog(sizes, first_pivot, "o-", color=RED,
                label="prvi element kao pivot")
    axes.loglog(sizes, random_pivot, "o-", color=BLUE,
                label="slučajan pivot")
    slope_first = np.polyfit(np.log(sizes), np.log(first_pivot), 1)[0]
    slope_random = np.polyfit(np.log(sizes), np.log(random_pivot), 1)[0]
    axes.text(sizes[1], first_pivot[3],
              f"nagib ≈ {slope_first:.2f}", color=RED, fontsize=15)
    axes.text(sizes[-2], random_pivot[-2] / 3.2,
              f"nagib ≈ {slope_random:.2f}", color=BLUE, fontsize=15)
    axes.set_xlabel("$n$ (sortiran ulaz)")
    axes.set_ylabel("broj poređenja")
    axes.legend(loc="upper left")
    save_figure(figure, "quicksort_loglog")


def figure_quicksort_partition() -> None:
    values = [7, 2, 9, 4, 1, 8, 5, 3, 6]
    pivot = 5
    figure, axes = create_blank_canvas((11, 4.6))
    for index, value in enumerate(values):
        color = VIOLET if value == pivot else MUTED_INK
        axes.bar(index, value, color=color, width=0.75, bottom=6)
    left = sorted([v for v in values if v < pivot], key=values.index)
    right = sorted([v for v in values if v > pivot], key=values.index)
    arranged = left + [pivot] + right
    for index, value in enumerate(arranged):
        color = BLUE if value < pivot else ORANGE
        color = VIOLET if value == pivot else color
        axes.bar(index, value, color=color, width=0.75, bottom=-5)
    axes.annotate("", xy=(4, 0.2), xytext=(4, 5.6),
                  arrowprops={"arrowstyle": "-|>", "color": INK, "lw": 2})
    axes.text(4.3, 3, "podela oko pivota", fontsize=14)
    axes.text(1.5, -6.2, "$< $ pivot", ha="center", color=BLUE, fontsize=16)
    axes.text(6.5, -6.2, "$> $ pivot", ha="center", color=ORANGE, fontsize=16)
    axes.set_xlim(-1, 9)
    axes.set_ylim(-7, 16)
    save_figure(figure, "quicksort_partition")


def figure_quicksort_indicator() -> None:
    figure, axes = create_blank_canvas((11, 3.4))
    size = 12
    i, j = 3, 9
    for rank in range(1, size + 1):
        inside = i <= rank <= j
        endpoint = rank in (i, j)
        color = ORANGE if endpoint else (BLUE if inside else GRID)
        axes.add_patch(Circle((rank, 0), 0.38, color=color))
        axes.text(rank, 0, f"$S_{{{rank}}}$", ha="center", va="center",
                  color="white" if inside else MUTED_INK, fontsize=13)
    axes.annotate("", xy=(i - 0.4, 0.9), xytext=(j + 0.4, 0.9),
                  arrowprops={"arrowstyle": "<->", "color": INK})
    axes.text((i + j) / 2, 1.15, "$j - i + 1$ elemenata", ha="center",
              fontsize=15)
    axes.text((i + j) / 2, -1.2,
              "poređeni $\\Leftrightarrow$ prvi izabran pivot među njima je "
              "$S_i$ ili $S_j$", ha="center", fontsize=15)
    axes.set_xlim(0.2, size + 0.8)
    axes.set_ylim(-1.7, 1.7)
    axes.set_aspect("equal")
    save_figure(figure, "quicksort_indicator")


def figure_er_samples() -> None:
    nodes = 30
    probabilities = [0.02, 0.05, 0.1, 0.3]
    figure, axes_row = plt.subplots(1, 4, figsize=(13, 3.8))
    for axes, probability in zip(axes_row, probabilities):
        graph = nx.gnp_random_graph(nodes, probability, seed=RANDOM_SEED)
        layout = nx.circular_layout(graph)
        largest = max(nx.connected_components(graph), key=len)
        colors = [ORANGE if node in largest else BLUE for node in graph]
        nx.draw_networkx_edges(graph, layout, ax=axes, edge_color=MUTED_INK,
                               alpha=0.5)
        nx.draw_networkx_nodes(graph, layout, ax=axes, node_size=60,
                               node_color=colors)
        axes.set_title(f"$p = {probability}$,  $np = {nodes * probability:g}$")
        axes.set_axis_off()
        axes.set_aspect("equal")
    save_figure(figure, "er_samples")


def figure_er_degrees() -> None:
    nodes, mean_degree = 5000, 8
    probability = mean_degree / (nodes - 1)
    graph = nx.fast_gnp_random_graph(nodes, probability, seed=RANDOM_SEED)
    degrees = np.array([d for _, d in graph.degree()])
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    k = np.arange(0, 22)
    counts = np.bincount(degrees, minlength=k.size)[: k.size] / nodes
    axes.bar(k, counts, color=BLUE, width=0.8, label="izmereno")
    poisson = [
        math.exp(-mean_degree) * mean_degree ** v / math.factorial(v)
        for v in k
    ]
    axes.plot(k, poisson, "o-", color=ORANGE, ms=7,
              label="Poisson$(\\lambda = np)$")
    axes.set_xlabel("stepen čvora $k$")
    axes.set_ylabel("$P(\\deg = k)$")
    axes.set_title(f"$G(n={nodes},\\ p={probability:.4f})$")
    axes.legend()
    save_figure(figure, "er_degrees")


def largest_component_fraction(nodes: int, mean_degree: float,
                               seed: int) -> float:
    probability = mean_degree / (nodes - 1)
    graph = nx.fast_gnp_random_graph(nodes, probability, seed=seed)
    largest = max(nx.connected_components(graph), key=len)
    return len(largest) / nodes


def giant_component_theory(mean_degree: float) -> float:
    if mean_degree <= 1:
        return 0.0
    else:
        fraction = 0.5
        for _ in range(200):
            fraction = 1 - math.exp(-mean_degree * fraction)
        return fraction


def figure_er_giant_component() -> None:
    mean_degrees = np.linspace(0.1, 3, 30)
    configurations = [(100, BLUE), (1000, AQUA), (10000, ORANGE)]
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    for nodes, color in configurations:
        fractions = [
            np.mean([
                largest_component_fraction(nodes, c, RANDOM_SEED + r)
                for r in range(ER_REPETITIONS)
            ])
            for c in mean_degrees
        ]
        axes.plot(mean_degrees, fractions, "o", color=color, ms=6,
                  label=f"$n = {nodes}$")
    fine = np.linspace(0.1, 3, 300)
    axes.plot(fine, [giant_component_theory(c) for c in fine], color=INK,
              label="$S = 1 - e^{-np\\,S}$")
    axes.axvline(1, color=MUTED_INK, ls="--")
    axes.set_xlabel("prosečan stepen $np$")
    axes.set_ylabel("udeo najveće komponente")
    axes.legend()
    save_figure(figure, "er_giant_component")


def figure_er_connectivity() -> None:
    offsets = np.linspace(-3, 4, 22)
    configurations = [(200, BLUE), (2000, ORANGE)]
    repetitions = ER_REPETITIONS * 3
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    for nodes, color in configurations:
        connected = []
        for c in offsets:
            probability = (math.log(nodes) + c) / nodes
            hits = sum(
                nx.is_connected(
                    nx.fast_gnp_random_graph(
                        nodes, probability, seed=RANDOM_SEED + r
                    )
                )
                for r in range(repetitions)
            )
            connected.append(hits / repetitions)
        axes.plot(offsets, connected, "o", color=color, ms=7,
                  label=f"$n = {nodes}$")
    fine = np.linspace(-3, 4, 300)
    axes.plot(fine, np.exp(-np.exp(-fine)), color=INK,
              label="$e^{-e^{-c}}$")
    axes.set_xlabel("$c$,   $p = (\\ln n + c)/n$")
    axes.set_ylabel("P(graf povezan)")
    axes.legend(loc="upper left")
    save_figure(figure, "er_connectivity")


@dataclass(frozen=True)
class FigureSpecification:
    name: str
    render: Callable[[], None]


FIGURE_REGISTRY = [
    FigureSpecification("scientific_cycle", figure_scientific_cycle),
    FigureSpecification("induction_deduction", figure_induction_deduction),
    FigureSpecification("experiment_variables", figure_experiment_variables),
    FigureSpecification("randomized_groups", figure_randomized_groups),
    FigureSpecification("random_variable_map", figure_random_variable_map),
    FigureSpecification("uniform", figure_uniform),
    FigureSpecification("uniform_samples", figure_uniform_samples),
    FigureSpecification("bernoulli", figure_bernoulli),
    FigureSpecification("binomial", figure_binomial),
    FigureSpecification("galton_board", figure_galton_board),
    FigureSpecification("normal_rule", figure_normal_rule),
    FigureSpecification("normal_parameters", figure_normal_parameters),
    FigureSpecification("white_noise", figure_white_noise),
    FigureSpecification("signal_plus_noise", figure_signal_plus_noise),
    FigureSpecification("noise_autocorrelation",
                        figure_noise_autocorrelation),
    FigureSpecification("central_limit", figure_central_limit),
    FigureSpecification("dice_sums", figure_dice_sums),
    FigureSpecification("standard_error", figure_standard_error),
    FigureSpecification("confidence_intervals", figure_confidence_intervals),
    FigureSpecification("p_value", figure_p_value),
    FigureSpecification("error_types", figure_error_types),
    FigureSpecification("accuracy_precision", figure_accuracy_precision),
    FigureSpecification("monte_carlo_pi", figure_monte_carlo_pi),
    FigureSpecification("quicksort_partition", figure_quicksort_partition),
    FigureSpecification("quicksort_indicator", figure_quicksort_indicator),
    FigureSpecification("quicksort_mean", figure_quicksort_mean),
    FigureSpecification("quicksort_distribution",
                        figure_quicksort_distribution),
    FigureSpecification("quicksort_loglog", figure_quicksort_loglog),
    FigureSpecification("er_samples", figure_er_samples),
    FigureSpecification("er_degrees", figure_er_degrees),
    FigureSpecification("er_giant_component", figure_er_giant_component),
    FigureSpecification("er_connectivity", figure_er_connectivity),
]


def select_figures() -> list[FigureSpecification]:
    wanted = {name for name in SELECTED_FIGURES.split(",") if name}
    if wanted:
        return [spec for spec in FIGURE_REGISTRY if spec.name in wanted]
    else:
        return list(FIGURE_REGISTRY)


def render_all_figures() -> int:
    failures = 0
    for specification in select_figures():
        random.seed(RANDOM_SEED)
        try:
            specification.render()
        except Exception:
            log.exception("figure %s failed", specification.name)
            failures += 1
    return failures


def main() -> int:
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    OUTPUT_DIRECTORY.mkdir(parents=True, exist_ok=True)
    configure_style()
    failures = render_all_figures()
    log.info("done, %d failures", failures)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
