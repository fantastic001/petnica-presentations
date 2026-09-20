from __future__ import annotations

import math
import random
import sys
from pathlib import Path
from typing import Callable

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import networkx as nx
import numpy as np
from matplotlib.patches import Circle

REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
if str(REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(REPOSITORY_ROOT))

from figures_framework.diagrams import (
    CycleDiagram,
    CycleLayout,
    DiagramNode,
    HubDiagram,
    HubSatellite,
    MappingDiagram,
    SequenceDiagram,
    SplitDiagram,
)
from figures_framework.layout import Side
from figures_framework import (
    DEFAULT_WIDE_SIZE,
    BoxSize,
    FigureContext,
    FigureRegistry,
    GridSpecification,
    binomial_pmf,
    environment_integer,
    harmonic_number,
    logarithmic_sample,
    normal_pdf,
    poisson_pmf,
    render_registry,
)

FIGURES = FigureRegistry("naucni-metod")
DEFAULT_OUTPUT_DIRECTORY = Path(__file__).parent / "img"
QUICKSORT_REPETITIONS = environment_integer("QUICKSORT_REPETITIONS", 30)
ER_REPETITIONS = environment_integer("ER_REPETITIONS", 20)


@FIGURES.register("scientific_cycle")
def render_scientific_cycle(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return CycleDiagram(
        steps=[
            DiagramNode("Posmatranje", palette.blue),
            DiagramNode("Pitanje", palette.violet),
            DiagramNode("Hipoteza", palette.orange),
            DiagramNode("Dizajn\neksperimenta", palette.aqua),
            DiagramNode("Eksperiment", palette.green),
            DiagramNode("Analiza", palette.yellow),
            DiagramNode("Zaključak\n→ teorija", palette.red),
        ],
        center_note="nove\npredikcije",
    ).render(context)


@FIGURES.register("induction_deduction")
def render_induction_deduction(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return CycleDiagram(
        steps=[
            DiagramNode("Teorija", palette.red),
            DiagramNode("Hipoteza", palette.orange),
            DiagramNode("Predikcija", palette.aqua),
            DiagramNode("Podaci / merenja", palette.blue),
            DiagramNode("Obrasci", palette.yellow),
            DiagramNode("Uopštavanje", palette.violet),
        ],
        layout=CycleLayout.COLUMNS,
        box_size=BoxSize(3.2, 1.0),
        side_notes=("DEDUKCIJA", "INDUKCIJA"),
    ).render(context)


@FIGURES.register("experiment_variables")
def render_experiment_variables(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return HubDiagram(
        center=DiagramNode("Sistem", palette.muted_ink),
        satellites=[
            HubSatellite(
                DiagramNode("Nezavisna\npromenljiva  $x$", palette.blue),
                Side.LEFT,
            ),
            HubSatellite(
                DiagramNode("Zavisna\npromenljiva  $y$", palette.orange),
                Side.RIGHT,
            ),
            HubSatellite(
                DiagramNode(
                    "Kontrolne promenljive  (fiksne)", palette.aqua
                ),
                Side.TOP,
                BoxSize(5.2, 0.9),
            ),
            HubSatellite(
                DiagramNode(
                    "Šum  $\\varepsilon$  (ne kontrolišemo)", palette.red
                ),
                Side.BOTTOM,
                BoxSize(5.2, 0.9),
            ),
        ],
        note="$y = f(x) + \\varepsilon$",
    ).render(context)


@FIGURES.register("randomized_groups")
def render_randomized_groups(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return SplitDiagram(
        source=DiagramNode("Uzorak", palette.muted_ink),
        splitter=DiagramNode("slučajna\npodela", palette.violet),
        groups=[
            DiagramNode("Tretman", palette.orange),
            DiagramNode("Kontrola", palette.blue),
        ],
    ).render(context)


@FIGURES.register("random_variable_map")
def render_random_variable_map(context: FigureContext) -> plt.Figure:
    return MappingDiagram(
        symbols=["⚀", "⚁", "⚂", "⚃", "⚄", "⚅"],
        values=[1, 2, 3, 4, 5, 6],
        domain_label="$\\Omega$ — ishodi",
        codomain_label="$\\mathbb{R}$",
        note="$X:\\ \\Omega \\to \\mathbb{R}$",
    ).render(context)


@FIGURES.register("uniform")
def render_uniform(context: FigureContext) -> plt.Figure:
    palette = context.palette
    figure, (left, right) = context.create_figure(
        DEFAULT_WIDE_SIZE, GridSpecification(1, 2)
    )
    faces = np.arange(1, 7)
    left.bar(faces, np.full(6, 1 / 6), color=palette.blue, width=0.7)
    left.set_title("Diskretna: kocka")
    left.set_xlabel("$k$")
    left.set_ylabel("$P(X=k)$")
    left.set_ylim(0, 0.3)
    x = np.linspace(-0.5, 3.5, 800)
    density = np.where((x >= 1) & (x <= 3), 0.5, 0.0)
    right.fill_between(x, density, color=palette.orange, alpha=0.25)
    right.plot(x, density, color=palette.orange)
    right.set_title("Neprekidna: $U(a,b)$")
    right.set_xticks([1, 3], ["$a$", "$b$"])
    right.set_yticks([0.5], ["$\\frac{1}{b-a}$"])
    right.set_ylim(0, 0.8)
    return figure


@FIGURES.register("uniform_samples")
def render_uniform_samples(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    sample_sizes = [10, 100, 10000]
    figure, axes_row = context.create_figure(
        DEFAULT_WIDE_SIZE,
        GridSpecification(1, 3, shared_axis="y"),
    )
    for axes, size in zip(axes_row, sample_sizes):
        rolls = generator.integers(1, 7, size=size)
        counts = np.bincount(rolls, minlength=7)[1:] / size
        axes.bar(np.arange(1, 7), counts, color=palette.blue, width=0.7)
        axes.axhline(1 / 6, color=palette.orange, ls="--")
        axes.set_title(f"$n = {size}$")
        axes.set_xticks(range(1, 7))
    axes_row[0].set_ylabel("relativna frekvencija")
    return figure


@FIGURES.register("bernoulli")
def render_bernoulli(context: FigureContext) -> plt.Figure:
    palette = context.palette
    figure, axes = context.create_figure((6, 4.4))
    probability = 0.3
    axes.bar(
        [0, 1],
        [1 - probability, probability],
        color=[palette.blue, palette.orange],
        width=0.55,
    )
    axes.set_xticks([0, 1], ["0\n(neuspeh)", "1\n(uspeh)"])
    axes.set_yticks([probability, 1 - probability], ["$p$", "$1-p$"])
    axes.set_ylim(0, 1)
    axes.set_title("$X \\sim \\mathrm{Bernoulli}(p)$")
    return figure


@FIGURES.register("binomial")
def render_binomial(context: FigureContext) -> plt.Figure:
    palette = context.palette
    trials = 20
    parameters = [
        (0.2, palette.blue), (0.5, palette.orange), (0.8, palette.aqua),
    ]
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    k = np.arange(trials + 1)
    width = 0.28
    for offset, (probability, color) in zip([-1, 0, 1], parameters):
        axes.bar(k + offset * width, binomial_pmf(trials, probability),
                 width=width, color=color, label=f"$p={probability}$")
    axes.set_xlabel("$k$ — broj uspeha od $n=20$")
    axes.set_ylabel("$P(X=k)$")
    axes.legend()
    return figure


@FIGURES.register("galton_board")
def render_galton_board(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    rows = 12
    balls = 5000
    positions = generator.binomial(rows, 0.5, size=balls)
    figure, (board, histogram) = context.create_figure(
        DEFAULT_WIDE_SIZE, GridSpecification(1, 2, (1, 1.3,))
    )
    board.set_axis_off()
    board.grid(False)
    for row in range(rows):
        for pin in range(row + 1):
            board.scatter(pin - row / 2, -row, s=18, color=palette.muted_ink)
    path_x = 0.0
    for row in range(rows):
        step = generator.choice([-0.5, 0.5])
        board.plot(
            [path_x, path_x + step], [-row, -row - 1],
            color=palette.orange, lw=2.5,
        )
        path_x += step
    board.set_title("Galtonova tabla")
    counts = np.bincount(positions, minlength=rows + 1) / balls
    histogram.bar(np.arange(rows + 1), counts, color=palette.blue, width=0.8,
                  label="simulacija")
    histogram.plot(np.arange(rows + 1), binomial_pmf(rows, 0.5), "o",
                   color=palette.orange, ms=8, label="$B(12, 1/2)$")
    histogram.set_xlabel("pregrada $k$")
    histogram.legend()
    return figure


@FIGURES.register("normal_rule")
def render_normal_rule(context: FigureContext) -> plt.Figure:
    palette = context.palette
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    x = np.linspace(-4, 4, 1000)
    y = normal_pdf(x, 0, 1)
    bands = [(3, "#dbe8f8", "99.7%"), (2, "#9fc2ec", "95%"),
             (1, palette.blue, "68%")]
    for width, color, label in bands:
        mask = np.abs(x) <= width
        axes.fill_between(x[mask], y[mask], color=color)
    axes.plot(x, y, color=palette.ink)
    for width, _, label in bands:
        level = -0.045 * width
        axes.annotate(
            "", xy=(-width, level), xytext=(width, level),
            arrowprops={"arrowstyle": "<->", "color": palette.ink},
        )
        axes.text(width + 0.12, level, label, va="center", fontsize=13,
                  color=palette.ink)
    axes.set_ylim(-0.16, 0.43)
    axes.spines["bottom"].set_visible(False)
    axes.spines["left"].set_visible(False)
    axes.set_xticks(range(-3, 4), [
        "$\\mu-3\\sigma$", "$\\mu-2\\sigma$", "$\\mu-\\sigma$", "$\\mu$",
        "$\\mu+\\sigma$", "$\\mu+2\\sigma$", "$\\mu+3\\sigma$",
    ])
    axes.set_yticks([])
    return figure


@FIGURES.register("normal_parameters")
def render_normal_parameters(context: FigureContext) -> plt.Figure:
    palette = context.palette
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    x = np.linspace(-6, 8, 1000)
    parameters = [
        (0, 1, palette.blue), (0, 2, palette.orange), (3, 0.6, palette.aqua),
    ]
    for mean, deviation, color in parameters:
        axes.plot(x, normal_pdf(x, mean, deviation), color=color,
                  label=f"$\\mu={mean},\\ \\sigma={deviation}$")
    axes.set_xlabel("$x$")
    axes.set_ylabel("$f(x)$")
    axes.legend()
    return figure


@FIGURES.register("white_noise")
def render_white_noise(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    samples = 300
    noise = generator.normal(0, 1, size=samples)
    figure, (series, histogram) = context.create_figure(
        DEFAULT_WIDE_SIZE, GridSpecification(1, 2, (2.2, 1,), shared_axis="y")
    )
    series.plot(noise, color=palette.blue, lw=1.2)
    series.set_xlabel("vreme $t$")
    series.set_ylabel("$\\varepsilon_t$")
    series.set_title("$\\varepsilon_t \\sim N(0, \\sigma^2)$, nezavisni")
    bins = np.linspace(-4, 4, 25)
    histogram.hist(
        noise, bins=bins, orientation="horizontal", color=palette.blue,
        density=True, alpha=0.6,
    )
    y = np.linspace(-4, 4, 200)
    histogram.plot(normal_pdf(y, 0, 1), y, color=palette.orange)
    histogram.set_title("raspodela")
    return figure


@FIGURES.register("signal_plus_noise")
def render_signal_plus_noise(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    t = np.linspace(0, 10, 120)
    signal = 2 * np.sin(t * 0.8) + 0.3 * t
    measured = signal + generator.normal(0, 0.8, size=t.size)
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    axes.scatter(t, measured, s=22, color=palette.blue, label="merenje $y$")
    axes.plot(t, signal, color=palette.orange, lw=3, label="zakon $f(t)$")
    axes.set_xlabel("$t$")
    axes.legend()
    axes.set_title("$y = f(t) + \\varepsilon$")
    return figure


@FIGURES.register("noise_autocorrelation")
def render_noise_autocorrelation(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    samples = 2000
    white = generator.normal(size=samples)
    walk = np.cumsum(generator.normal(size=samples))
    figure, (white_axes, walk_axes) = context.create_figure(
        DEFAULT_WIDE_SIZE, GridSpecification(1, 2)
    )
    white_axes.scatter(
        white[:-1], white[1:], s=5, color=palette.blue, alpha=0.5
    )
    white_axes.set_title("beli šum: $\\varepsilon_t$ vs $\\varepsilon_{t+1}$")
    walk_axes.scatter(
        walk[:-1], walk[1:], s=5, color=palette.orange, alpha=0.5
    )
    walk_axes.set_title("nije beli šum: $x_t$ vs $x_{t+1}$")
    for axes in (white_axes, walk_axes):
        axes.set_aspect("equal", adjustable="datalim")
    return figure


@FIGURES.register("central_limit")
def render_central_limit(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    sample_sizes = [1, 2, 5, 30]
    repetitions = 20000
    figure, axes_row = context.create_figure((12, 3.8), GridSpecification(1, 4))
    for axes, size in zip(axes_row, sample_sizes):
        means = generator.exponential(1, size=(repetitions, size)).mean(1)
        axes.hist(means, bins=60, density=True, color=palette.blue, alpha=0.75)
        x = np.linspace(0, 4, 400)
        if size >= 5:
            axes.plot(x, normal_pdf(x, 1, 1 / math.sqrt(size)),
                      color=palette.orange)
        else:
            axes.plot([], [])
        axes.set_xlim(0, 4)
        axes.set_yticks([])
        axes.set_title(f"$n = {size}$")
    axes_row[0].set_xlabel("$\\bar{X}_n$, $X_i \\sim \\mathrm{Exp}(1)$")
    return figure


@FIGURES.register("dice_sums")
def render_dice_sums(context: FigureContext) -> plt.Figure:
    palette = context.palette
    figure, axes_row = context.create_figure((12, 3.8), GridSpecification(1, 4))
    distribution = np.full(6, 1 / 6)
    single_die = np.full(6, 1 / 6)
    for index, axes in enumerate(axes_row):
        dice = index + 1 if index < 3 else 10
        current = single_die
        for _ in range(dice - 1):
            current = np.convolve(current, distribution)
        support = np.arange(dice, 6 * dice + 1)
        axes.bar(support, current, color=palette.blue, width=0.8)
        axes.set_title(f"zbir {dice} kock{'a' if dice > 1 else 'e'}")
        axes.set_yticks([])
    return figure


@FIGURES.register("standard_error")
def render_standard_error(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    sample_sizes = [2, 5, 10, 20, 50, 100, 200, 500]
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    for size in sample_sizes:
        means = generator.normal(10, 2, size=(40, size)).mean(1)
        jitter = generator.uniform(-0.03, 0.03, size=means.size)
        axes.scatter(size * (1 + jitter), means, s=16, color=palette.blue,
                     alpha=0.7)
    n = np.logspace(math.log10(2), math.log10(500), 200)
    axes.plot(n, 10 + 2 * 2 / np.sqrt(n), color=palette.orange,
              label="$\\mu \\pm 2\\sigma/\\sqrt{n}$")
    axes.plot(n, 10 - 2 * 2 / np.sqrt(n), color=palette.orange)
    axes.set_xscale("log")
    axes.set_xlabel("veličina uzorka $n$")
    axes.set_ylabel("$\\bar{x}$")
    axes.legend()
    return figure


@FIGURES.register("confidence_intervals")
def render_confidence_intervals(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.spawn_random(3)
    true_mean, deviation, size, intervals = 10, 2, 25, 30
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    half_width = 1.96 * deviation / math.sqrt(size)
    for index in range(intervals):
        mean = generator.normal(true_mean, deviation, size=size).mean()
        misses = abs(mean - true_mean) > half_width
        color = palette.red if misses else palette.blue
        axes.plot([index, index], [mean - half_width, mean + half_width],
                  color=color, lw=3)
        axes.scatter(index, mean, color=color, s=30, zorder=3)
    axes.axhline(true_mean, color=palette.ink, ls="--", label="pravo $\\mu$")
    axes.set_xlabel("ponovljeni eksperiment")
    axes.set_ylabel("95% interval")
    axes.legend(loc="upper right")
    return figure


@FIGURES.register("p_value")
def render_p_value(context: FigureContext) -> plt.Figure:
    palette = context.palette
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    x = np.linspace(-4, 4, 1000)
    y = normal_pdf(x, 0, 1)
    observed = 2.2
    axes.plot(x, y, color=palette.ink)
    axes.fill_between(x[x >= observed], y[x >= observed], color=palette.orange)
    axes.fill_between(
        x[x <= -observed],
        y[x <= -observed],
        color=palette.orange,
    )
    axes.axvline(observed, color=palette.blue, lw=2.5)
    axes.text(
        observed + 0.1,
        0.3,
        "izmereno $t$",
        color=palette.blue,
        fontsize=15,
    )
    axes.annotate("p-vrednost", xy=(2.6, 0.012), xytext=(2.6, 0.15),
                  ha="center", fontsize=15,
                  arrowprops={"arrowstyle": "->", "color": palette.ink})
    axes.text(-3.9, 0.35, "raspodela statistike\nako važi $H_0$",
              fontsize=14, color=palette.muted_ink)
    axes.set_yticks([])
    return figure


@FIGURES.register("error_types")
def render_error_types(context: FigureContext) -> plt.Figure:
    palette = context.palette
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    x = np.linspace(-4, 7, 1200)
    null = normal_pdf(x, 0, 1)
    alternative = normal_pdf(x, 3, 1)
    threshold = 1.645
    axes.plot(x, null, color=palette.blue, label="$H_0$ tačna")
    axes.plot(x, alternative, color=palette.orange, label="$H_1$ tačna")
    axes.fill_between(
        x[x >= threshold], null[x >= threshold], color=palette.blue,
        alpha=0.45,
    )
    axes.fill_between(x[x <= threshold], alternative[x <= threshold],
                      color=palette.orange, alpha=0.45)
    axes.axvline(threshold, color=palette.ink, ls="--")
    axes.text(2.1, 0.03, "$\\alpha$", fontsize=20, color=palette.blue)
    axes.text(0.9, 0.03, "$\\beta$", fontsize=20, color=palette.orange)
    axes.text(threshold + 0.1, 0.42, "prag odluke", fontsize=13)
    axes.set_yticks([])
    axes.legend(loc="upper left")
    return figure


@FIGURES.register("accuracy_precision")
def render_accuracy_precision(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    cases = [
        ("tačno i precizno", 0.0, 0.15),
        ("netačno, precizno", 0.9, 0.15),
        ("tačno, neprecizno", 0.0, 0.6),
        ("netačno i neprecizno", 0.9, 0.6),
    ]
    figure, axes_row = context.create_figure((12, 3.6), GridSpecification(1, 4))
    for axes, (title, bias, spread) in zip(axes_row, cases):
        axes.set_axis_off()
        axes.grid(False)
        for ring, color in zip([2, 1.4, 0.8, 0.25],
                               ["#eef3fb", "#cfdff4", "#9fc2ec", palette.blue]):
            axes.add_patch(Circle((0, 0), ring, color=color))
        shots = generator.normal([bias, bias * 0.6], spread, size=(12, 2))
        axes.scatter(shots[:, 0], shots[:, 1], color=palette.orange, s=40,
                     edgecolor="white", zorder=3)
        axes.set_xlim(-2.1, 2.1)
        axes.set_ylim(-2.1, 2.1)
        axes.set_aspect("equal")
        axes.set_title(title, fontsize=14)
    return figure


@FIGURES.register("monte_carlo_pi")
def render_monte_carlo_pi(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    points = generator.uniform(0, 1, size=(3000, 2))
    inside = (points ** 2).sum(1) <= 1
    figure, (scatter, convergence) = context.create_figure(
        DEFAULT_WIDE_SIZE, GridSpecification(1, 2, (1, 1.5,))
    )
    scatter.scatter(*points[inside].T, s=3, color=palette.blue)
    scatter.scatter(*points[~inside].T, s=3, color=palette.orange)
    scatter.set_aspect("equal")
    scatter.set_title("$\\pi \\approx 4 \\cdot$ unutra / ukupno")
    many = generator.uniform(0, 1, size=(200000, 2))
    hits = np.cumsum((many ** 2).sum(1) <= 1)
    n = np.arange(1, many.shape[0] + 1)
    estimate = 4 * hits / n
    visible = logarithmic_sample(n.size)
    convergence.plot(n[visible - 1], estimate[visible - 1], color=palette.blue,
                     lw=1.4, label="procena")
    convergence.axhline(math.pi, color=palette.ink, ls="--", label="$\\pi$")
    band = 1.96 * 4 * math.sqrt(math.pi / 4 * (1 - math.pi / 4)) / np.sqrt(n)
    convergence.fill_between(
        n[visible - 1], math.pi - band[visible - 1],
        math.pi + band[visible - 1], color=palette.orange, alpha=0.2,
        label="$\\pm 2\\,SE$",
    )
    convergence.set_xscale("log")
    convergence.set_ylim(2.6, 3.7)
    convergence.set_xlabel("broj tačaka $n$")
    convergence.legend()
    return figure


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
    return 2 * (size + 1) * harmonic_number(size) - 4 * size


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


@FIGURES.register("quicksort_mean")
def render_quicksort_mean(context: FigureContext) -> plt.Figure:
    palette = context.palette
    measurements = measure_quicksort(
        QUICKSORT_SIZES, choose_random_pivot, build_shuffled_input,
        QUICKSORT_REPETITIONS,
    )
    sizes = np.array(QUICKSORT_SIZES)
    figure, (absolute, ratio) = context.create_figure(
        DEFAULT_WIDE_SIZE, GridSpecification(1, 2)
    )
    means = measurements.mean(1)
    deviations = measurements.std(1, ddof=1)
    absolute.errorbar(sizes, means, yerr=2 * deviations, fmt="o",
                      color=palette.blue, ms=8, capsize=4, label="merenje")
    theory = [expected_quicksort_comparisons(int(n)) for n in sizes]
    absolute.plot(
        sizes,
        theory,
        color=palette.orange,
        label="$E[C_n]$ (teorija)",
    )
    absolute.set_xlabel("$n$")
    absolute.set_ylabel("broj poređenja $C_n$")
    absolute.legend()
    normalized = measurements / (sizes * np.log(sizes))[:, None]
    ratio.errorbar(
        sizes, normalized.mean(1), yerr=2 * normalized.std(1, ddof=1),
        fmt="o", color=palette.blue, ms=8, capsize=4,
    )
    ratio.plot(sizes, np.array(theory) / (sizes * np.log(sizes)),
               color=palette.orange)
    ratio.axhline(2, color=palette.ink, ls="--")
    ratio.set_xscale("log")
    ratio.set_xlabel("$n$")
    ratio.set_ylabel("$C_n / (n \\ln n)$")
    return figure


@FIGURES.register("quicksort_distribution")
def render_quicksort_distribution(context: FigureContext) -> plt.Figure:
    palette = context.palette
    size, repetitions = 2000, 2000
    measurements = measure_quicksort(
        [size], choose_random_pivot, build_shuffled_input, repetitions
    )[0]
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    axes.hist(
        measurements,
        bins=45,
        color=palette.blue,
        alpha=0.75,
        density=True,
    )
    axes.axvline(
        expected_quicksort_comparisons(size), color=palette.orange, lw=3,
        label="$E[C_n]$ teorija",
    )
    axes.set_xlabel(f"broj poređenja, $n = {size}$, {repetitions} ponavljanja")
    axes.set_yticks([])
    axes.legend()
    return figure


@FIGURES.register("quicksort_loglog")
def render_quicksort_loglog(context: FigureContext) -> plt.Figure:
    palette = context.palette
    sizes = [100, 200, 400, 800, 1600, 3200]
    random_pivot = measure_quicksort(sizes, choose_random_pivot,
                                     build_sorted_input, 5).mean(1)
    first_pivot = measure_quicksort(sizes, choose_first_pivot,
                                    build_sorted_input, 1).mean(1)
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    axes.loglog(sizes, first_pivot, "o-", color=palette.red,
                label="prvi element kao pivot")
    axes.loglog(sizes, random_pivot, "o-", color=palette.blue,
                label="slučajan pivot")
    slope_first = np.polyfit(np.log(sizes), np.log(first_pivot), 1)[0]
    slope_random = np.polyfit(np.log(sizes), np.log(random_pivot), 1)[0]
    axes.text(sizes[1], first_pivot[3],
              f"nagib ≈ {slope_first:.2f}", color=palette.red, fontsize=15)
    axes.text(sizes[-2], random_pivot[-2] / 3.2,
              f"nagib ≈ {slope_random:.2f}", color=palette.blue, fontsize=15)
    axes.set_xlabel("$n$ (sortiran ulaz)")
    axes.set_ylabel("broj poređenja")
    axes.legend(loc="upper left")
    return figure


@FIGURES.register("quicksort_partition")
def render_quicksort_partition(context: FigureContext) -> plt.Figure:
    palette = context.palette
    values = [7, 2, 9, 4, 1, 8, 5, 3, 6]
    pivot = 5
    canvas = context.blank_canvas((11, 4.6))
    axes = canvas.axes
    for index, value in enumerate(values):
        color = palette.violet if value == pivot else palette.muted_ink
        axes.bar(index, value, color=color, width=0.75, bottom=6)
    left = sorted([v for v in values if v < pivot], key=values.index)
    right = sorted([v for v in values if v > pivot], key=values.index)
    arranged = left + [pivot] + right
    for index, value in enumerate(arranged):
        color = palette.blue if value < pivot else palette.orange
        color = palette.violet if value == pivot else color
        axes.bar(index, value, color=color, width=0.75, bottom=-5)
    axes.annotate(
        "", xy=(4, 0.2), xytext=(4, 5.6),
        arrowprops={"arrowstyle": "-|>", "color": palette.ink, "lw": 2},
    )
    axes.text(4.3, 3, "podela oko pivota", fontsize=14)
    axes.text(
        1.5,
        -6.2,
        "$< $ pivot",
        ha="center",
        color=palette.blue,
        fontsize=16,
    )
    axes.text(
        6.5,
        -6.2,
        "$> $ pivot",
        ha="center",
        color=palette.orange,
        fontsize=16,
    )
    axes.set_xlim(-1, 9)
    axes.set_ylim(-7, 16)
    return canvas.figure


@FIGURES.register("quicksort_indicator")
def render_quicksort_indicator(context: FigureContext) -> plt.Figure:
    return SequenceDiagram(
        length=12,
        highlighted=(3, 9),
        span_caption="$j - i + 1$ elemenata",
        note="poređeni $\\Leftrightarrow$ prvi izabran pivot među njima je "
             "$S_i$ ili $S_j$",
    ).render(context)


@FIGURES.register("er_samples")
def render_er_samples(context: FigureContext) -> plt.Figure:
    palette = context.palette
    nodes = 30
    probabilities = [0.02, 0.05, 0.1, 0.3]
    figure, axes_row = context.create_figure((13, 3.8), GridSpecification(1, 4))
    for axes, probability in zip(axes_row, probabilities):
        graph = nx.gnp_random_graph(nodes, probability, seed=context.seed)
        layout = nx.circular_layout(graph)
        largest = max(nx.connected_components(graph), key=len)
        colors = [
            palette.orange if node in largest else palette.blue
            for node in graph
        ]
        nx.draw_networkx_edges(
            graph, layout, ax=axes, edge_color=palette.muted_ink, alpha=0.5
        )
        nx.draw_networkx_nodes(graph, layout, ax=axes, node_size=60,
                               node_color=colors)
        axes.set_title(f"$p = {probability}$,  $np = {nodes * probability:g}$")
        axes.set_axis_off()
        axes.set_aspect("equal")
    return figure


@FIGURES.register("er_degrees")
def render_er_degrees(context: FigureContext) -> plt.Figure:
    palette = context.palette
    nodes, mean_degree = 5000, 8
    probability = mean_degree / (nodes - 1)
    graph = nx.fast_gnp_random_graph(nodes, probability, seed=context.seed)
    degrees = np.array([d for _, d in graph.degree()])
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    k = np.arange(0, 22)
    counts = np.bincount(degrees, minlength=k.size)[: k.size] / nodes
    axes.bar(k, counts, color=palette.blue, width=0.8, label="izmereno")
    poisson = poisson_pmf(mean_degree, k)
    axes.plot(k, poisson, "o-", color=palette.orange, ms=7,
              label="Poisson$(\\lambda = np)$")
    axes.set_xlabel("stepen čvora $k$")
    axes.set_ylabel("$P(\\deg = k)$")
    axes.set_title(f"$G(n={nodes},\\ p={probability:.4f})$")
    axes.legend()
    return figure


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


@FIGURES.register("er_giant_component")
def render_er_giant_component(context: FigureContext) -> plt.Figure:
    palette = context.palette
    mean_degrees = np.linspace(0.1, 3, 30)
    configurations = [
        (100, palette.blue), (1000, palette.aqua), (10000, palette.orange),
    ]
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    for nodes, color in configurations:
        fractions = [
            np.mean([
                largest_component_fraction(nodes, c, context.seed + r)
                for r in range(ER_REPETITIONS)
            ])
            for c in mean_degrees
        ]
        axes.plot(mean_degrees, fractions, "o", color=color, ms=6,
                  label=f"$n = {nodes}$")
    fine = np.linspace(0.1, 3, 300)
    axes.plot(
        fine, [giant_component_theory(c) for c in fine], color=palette.ink,
        label="$S = 1 - e^{-np\\,S}$",
    )
    axes.axvline(1, color=palette.muted_ink, ls="--")
    axes.set_xlabel("prosečan stepen $np$")
    axes.set_ylabel("udeo najveće komponente")
    axes.legend()
    return figure


@FIGURES.register("er_connectivity")
def render_er_connectivity(context: FigureContext) -> plt.Figure:
    palette = context.palette
    offsets = np.linspace(-3, 4, 22)
    configurations = [(200, palette.blue), (2000, palette.orange)]
    repetitions = ER_REPETITIONS * 3
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    for nodes, color in configurations:
        connected = []
        for c in offsets:
            probability = (math.log(nodes) + c) / nodes
            hits = sum(
                nx.is_connected(
                    nx.fast_gnp_random_graph(
                        nodes, probability, seed=context.seed + r
                    )
                )
                for r in range(repetitions)
            )
            connected.append(hits / repetitions)
        axes.plot(offsets, connected, "o", color=color, ms=7,
                  label=f"$n = {nodes}$")
    fine = np.linspace(-3, 4, 300)
    axes.plot(fine, np.exp(-np.exp(-fine)), color=palette.ink,
              label="$e^{-e^{-c}}$")
    axes.set_xlabel("$c$,   $p = (\\ln n + c)/n$")
    axes.set_ylabel("P(graf povezan)")
    axes.legend(loc="upper left")
    return figure


def main() -> int:
    return render_registry(FIGURES, DEFAULT_OUTPUT_DIRECTORY)


if __name__ == "__main__":
    sys.exit(main())
