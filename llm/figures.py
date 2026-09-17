from __future__ import annotations

import logging
import math
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

SHARED_FIGURES_DIRECTORY = (
    Path(__file__).resolve().parent.parent / "naucni-metod"
)
sys.path.insert(0, str(SHARED_FIGURES_DIRECTORY))

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Circle, FancyBboxPatch

from figures import (
    AQUA,
    BLUE,
    GREEN,
    GRID,
    INK,
    MAGENTA,
    MUTED_INK,
    ORANGE,
    RED,
    SURFACE,
    VIOLET,
    YELLOW,
    configure_style,
    create_blank_canvas,
    draw_arrow,
    draw_box,
    point_between,
)

OUTPUT_DIRECTORY = Path(
    os.environ.get("LLM_FIGURES_OUTPUT_DIR", Path(__file__).parent / "img")
)
OUTPUT_FORMAT = os.environ.get("LLM_FIGURES_FORMAT", "svg")
FIGURE_DPI = int(os.environ.get("LLM_FIGURES_DPI", "150"))
RANDOM_SEED = int(os.environ.get("LLM_FIGURES_SEED", "7"))
SELECTED_FIGURES = os.environ.get("LLM_FIGURES_ONLY", "")
BIAS_VARIANCE_REPETITIONS = int(
    os.environ.get("BIAS_VARIANCE_REPETITIONS", "300")
)
FIGURE_SIZE_WIDE = (10, 4.6)
FIGURE_SIZE_DIAGRAM = (10, 5)

log = logging.getLogger("llm-figures")


def save_figure(figure: plt.Figure, name: str) -> None:
    path = OUTPUT_DIRECTORY / f"{name}.{OUTPUT_FORMAT}"
    figure.tight_layout()
    figure.savefig(path, format=OUTPUT_FORMAT, dpi=FIGURE_DPI)
    plt.close(figure)
    log.info("saved %s", path)


def draw_chain(axes, labels_and_colors, y=0.0, spacing=3.0, width=2.4,
               height=1.0) -> list[tuple[float, float]]:
    offset = spacing * (len(labels_and_colors) - 1) / 2
    centers = [
        (index * spacing - offset, y)
        for index in range(len(labels_and_colors))
    ]
    for (label, color), center in zip(labels_and_colors, centers):
        draw_box(axes, center, label, color, width=width, height=height)
    for start, end in zip(centers, centers[1:]):
        draw_arrow(
            axes,
            (start[0] + width / 2 + 0.05, y),
            (end[0] - width / 2 - 0.05, y),
        )
    return centers


def figure_model_map() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    figure, axes = create_blank_canvas(FIGURE_SIZE_DIAGRAM)
    cloud = generator.normal([-4, 0], [0.7, 0.9], size=(160, 2))
    axes.scatter(cloud[:, 0], cloud[:, 1], s=14, color=MUTED_INK, alpha=0.6)
    axes.text(-4, 2.3, "Svet", ha="center", fontsize=20, color=INK)
    axes.text(-4, -2.4, "složen, pun šuma", ha="center", fontsize=14,
              color=MUTED_INK)
    draw_arrow(axes, (-2.6, 0), (-1.3, 0))
    draw_box(axes, (0, 0), "Model\n$y = f(x)$", BLUE, 2.4, 1.4)
    axes.text(0, -1.4, "uprošćenje", ha="center", fontsize=14,
              color=MUTED_INK)
    draw_arrow(axes, (1.3, 0), (2.6, 0))
    draw_box(axes, (4, 0), "Predikcija", ORANGE, 2.4, 1.0)
    draw_arrow(axes, (4, -0.7), (-4, -1.4), color=AQUA, curve=-0.35)
    axes.text(0, -3.0, "proveravamo eksperimentom", ha="center",
              fontsize=14, color=AQUA)
    axes.set_xlim(-5.6, 5.6)
    axes.set_ylim(-3.4, 2.9)
    save_figure(figure, "model_map")


def figure_model_spectrum() -> None:
    figure, axes = create_blank_canvas((11, 3.6))
    gradient = np.linspace(0, 1, 256)[None, :]
    axes.imshow(gradient, extent=(-5, 5, -0.3, 0.3), cmap="Blues",
                aspect="auto")
    examples = [
        (-4.5, "$F = ma$", "Njutn"),
        (-2.3, "$y = ax + b$", "regresija"),
        (0.0, "stablo\nodlučivanja", "ML"),
        (2.3, "neuronska\nmreža", "duboko učenje"),
        (4.5, "LLM", "$10^{11}$ parametara"),
    ]
    for x, top, bottom in examples:
        axes.plot([x, x], [0.3, 0.55], color=INK, lw=1.5)
        axes.text(x, 0.65, top, ha="center", va="bottom", fontsize=15)
        axes.text(x, -0.45, bottom, ha="center", va="top", fontsize=13,
                  color=MUTED_INK)
    axes.text(-5, -1.35, "BELA KUTIJA: razumemo svaki deo", ha="left",
              fontsize=14, color=BLUE, fontweight="bold")
    axes.text(5, -1.35, "CRNA KUTIJA: radi, ali ne znamo zašto", ha="right",
              fontsize=14, color=INK, fontweight="bold")
    axes.set_xlim(-5.4, 5.4)
    axes.set_ylim(-1.6, 1.6)
    save_figure(figure, "model_spectrum")


def figure_programming_vs_learning() -> None:
    figure, axes = create_blank_canvas(FIGURE_SIZE_DIAGRAM)
    axes.text(-5.3, 1.6, "Klasično\nprogramiranje", fontsize=15,
              va="center", color=INK)
    draw_box(axes, (-1.2, 2.3), "pravila", BLUE, 2.0, 0.8)
    draw_box(axes, (-1.2, 0.9), "podaci", AQUA, 2.0, 0.8)
    draw_box(axes, (1.8, 1.6), "program", MUTED_INK, 2.0, 1.0)
    draw_box(axes, (4.6, 1.6), "odgovori", ORANGE, 2.0, 0.8)
    draw_arrow(axes, (-0.15, 2.2), (0.75, 1.75))
    draw_arrow(axes, (-0.15, 1.0), (0.75, 1.45))
    draw_arrow(axes, (2.85, 1.6), (3.55, 1.6))
    axes.plot([-5.4, 5.8], [0, 0], color=GRID, lw=2)
    axes.text(-5.3, -1.6, "Mašinsko\nučenje", fontsize=15, va="center",
              color=INK)
    draw_box(axes, (-1.2, -0.9), "podaci", AQUA, 2.0, 0.8)
    draw_box(axes, (-1.2, -2.3), "odgovori", ORANGE, 2.0, 0.8)
    draw_box(axes, (1.8, -1.6), "učenje", MUTED_INK, 2.0, 1.0)
    draw_box(axes, (4.6, -1.6), "pravila", BLUE, 2.0, 0.8)
    draw_arrow(axes, (-0.15, -1.0), (0.75, -1.45))
    draw_arrow(axes, (-0.15, -2.2), (0.75, -1.75))
    draw_arrow(axes, (2.85, -1.6), (3.55, -1.6))
    axes.set_xlim(-5.5, 5.9)
    axes.set_ylim(-3, 3)
    save_figure(figure, "programming_vs_learning")


def figure_fitting_loss() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    x = np.linspace(0, 10, 25)
    y = 0.8 * x + 1 + generator.normal(0, 1.2, size=x.size)
    slope = 0.8
    figure, (fit, loss) = plt.subplots(1, 2, figsize=FIGURE_SIZE_WIDE)
    prediction = slope * x + 1
    for xi, yi, pi in zip(x, y, prediction):
        fit.plot([xi, xi], [yi, pi], color=ORANGE, lw=1.5)
    fit.scatter(x, y, color=BLUE, s=30, zorder=3)
    fit.plot(x, prediction, color=INK)
    fit.set_title("greška = rastojanje do prave")
    fit.set_xlabel("$x$")
    fit.set_ylabel("$y$")
    slopes = np.linspace(-0.2, 1.8, 200)
    losses = [np.mean((y - (s * x + 1)) ** 2) for s in slopes]
    loss.plot(slopes, losses, color=INK)
    current = -0.1
    for _ in range(6):
        gradient = np.mean(-2 * x * (y - (current * x + 1)))
        value = np.mean((y - (current * x + 1)) ** 2)
        loss.scatter(current, value, color=ORANGE, s=60, zorder=3)
        next_value = current - 0.006 * gradient
        next_loss = np.mean((y - (next_value * x + 1)) ** 2)
        loss.annotate("", xy=(next_value, next_loss), xytext=(current, value),
                      arrowprops={"arrowstyle": "->", "color": ORANGE})
        current = next_value
    loss.set_title("učenje = spuštanje niz grešku")
    loss.set_xlabel("parametar $a$")
    loss.set_ylabel("greška $L(a)$")
    save_figure(figure, "fitting_loss")


def figure_neural_network() -> None:
    figure, axes = create_blank_canvas(FIGURE_SIZE_DIAGRAM)
    layers = [3, 5, 5, 2]
    colors = [AQUA, BLUE, BLUE, ORANGE]
    positions = []
    for index, (size, color) in enumerate(zip(layers, colors)):
        x = index * 3
        ys = np.linspace(-(size - 1) / 2, (size - 1) / 2, size) * 1.1
        positions.append([(x, y) for y in ys])
    for left, right in zip(positions, positions[1:]):
        for a in left:
            for b in right:
                axes.plot([a[0], b[0]], [a[1], b[1]], color=GRID, lw=1.2,
                          zorder=1)
    for layer, color in zip(positions, colors):
        for point in layer:
            axes.add_patch(Circle(point, 0.32, color=color, zorder=2))
    labels = ["ulaz", "skriveni slojevi", "", "izlaz"]
    for index, label in enumerate(labels):
        if label:
            x = index * 3 + (1.5 if index == 1 else 0)
            axes.text(x, -3.4, label, ha="center", fontsize=15,
                      color=MUTED_INK)
        else:
            continue
    axes.text(4.5, 3.4, "neuron: $y = \\max(0,\\ w_1 x_1 + w_2 x_2 + b)$",
              ha="center", fontsize=16)
    axes.set_xlim(-1, 10)
    axes.set_ylim(-3.9, 3.9)
    axes.set_aspect("equal")
    save_figure(figure, "neural_network")


def figure_next_token() -> None:
    candidates = [
        ("Valjeva", 0.71), ("Beograda", 0.08), ("reke", 0.06),
        ("Novog Sada", 0.03), ("mora", 0.01),
    ]
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    words = [word for word, _ in candidates][::-1]
    probabilities = [p for _, p in candidates][::-1]
    colors = [MUTED_INK] * (len(words) - 1) + [ORANGE]
    axes.barh(words, probabilities, color=colors, height=0.6)
    for index, probability in enumerate(probabilities):
        axes.text(probability + 0.01, index, f"{probability:.2f}",
                  va="center", fontsize=15)
    axes.set_title("„Petnica se nalazi pored ___”", fontsize=20)
    axes.set_xlabel("$P(\\mathrm{reč} \\mid \\mathrm{prethodne\\ reči})$")
    axes.set_xlim(0, 0.85)
    axes.grid(axis="y", visible=False)
    save_figure(figure, "next_token")


def figure_language_model_timeline() -> None:
    events = [
        (1948, "Šenon:\nn-grami", BLUE),
        (1966, "ELIZA", MUTED_INK),
        (1997, "LSTM", VIOLET),
        (2013, "word2vec", AQUA),
        (2017, "Transformer", ORANGE),
        (2020, "GPT-3", RED),
        (2022, "ChatGPT", GREEN),
        (2026, "agenti", YELLOW),
    ]
    figure, axes = create_blank_canvas((12, 3.4))
    axes.plot([-0.5, len(events) - 0.5], [0, 0], color=INK, lw=2)
    for index, (year, label, color) in enumerate(events):
        side = 1 if index % 2 == 0 else -1
        axes.scatter(index, 0, s=160, color=color, zorder=3)
        axes.plot([index, index], [0, 0.55 * side], color=color, lw=1.5)
        axes.text(index, 0.7 * side, label, ha="center",
                  va="bottom" if side > 0 else "top", fontsize=15)
        axes.text(index, -0.25 * side, str(year), ha="center",
                  va="top" if side > 0 else "bottom", fontsize=13,
                  color=MUTED_INK)
    axes.set_xlim(-0.8, len(events) - 0.2)
    axes.set_ylim(-1.8, 1.8)
    save_figure(figure, "language_model_timeline")


def scaling_loss(compute: np.ndarray, parameters: float) -> np.ndarray:
    capacity_term = 400 / parameters ** 0.34
    data_term = 2.6e3 / (compute / (6 * parameters)) ** 0.28
    return 1.7 + capacity_term + data_term


def figure_scaling_law() -> None:
    compute = np.logspace(18, 26, 200)
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    sizes = [(1e8, AQUA, "$10^8$"), (1e9, BLUE, "$10^9$"),
             (1e10, VIOLET, "$10^{10}$"), (1e11, ORANGE, "$10^{11}$")]
    for parameters, color, label in sizes:
        loss = scaling_loss(compute, parameters)
        start = compute >= 6 * parameters * 2e8
        axes.plot(compute[start], loss[start], color=color,
                  label=f"$N = ${label}")
    envelope = np.min(
        [scaling_loss(compute, n) for n in np.logspace(7, 13, 120)], axis=0
    )
    axes.plot(compute, envelope, color=INK, ls="--", lw=3,
              label="najbolje za dato $C$")
    axes.set_xscale("log")
    axes.set_yscale("log")
    axes.set_ylim(1.6, 8)
    axes.yaxis.set_major_formatter(plt.ScalarFormatter())
    axes.yaxis.set_minor_formatter(plt.NullFormatter())
    axes.set_yticks([2, 3, 4, 6, 8])
    axes.set_xlabel("računanje $C$ (FLOP)")
    axes.set_ylabel("greška $L$")
    axes.set_title("ilustracija zakona skaliranja")
    axes.legend(ncol=2, fontsize=13)
    save_figure(figure, "scaling_law")


def figure_attention_heatmap() -> None:
    tokens = ["Mačka", "nije", "pojela", "ribu", "jer", "je", "bila", "sita"]
    size = len(tokens)
    weights = np.full((size, size), 0.02)
    focus = {
        0: {0: 1.0}, 1: {1: 0.6, 2: 0.4}, 2: {2: 0.5, 0: 0.3, 3: 0.2},
        3: {3: 0.5, 2: 0.5}, 4: {4: 0.5, 2: 0.3, 1: 0.2},
        5: {0: 0.8, 3: 0.1, 5: 0.1}, 6: {6: 0.4, 0: 0.4, 5: 0.2},
        7: {0: 0.7, 7: 0.2, 6: 0.1},
    }
    for row, columns in focus.items():
        for column, value in columns.items():
            weights[row, column] = value
    mask = np.triu(np.ones((size, size), dtype=bool), k=1)
    weights = np.where(mask, np.nan, weights)
    weights = weights / np.nansum(weights, axis=1, keepdims=True)
    figure, axes = plt.subplots(figsize=(7.4, 6.4))
    axes.grid(False)
    image = axes.imshow(weights, cmap="Blues", vmin=0, vmax=0.8)
    axes.set_xticks(range(size), tokens, rotation=45, ha="right")
    axes.set_yticks(range(size), tokens)
    axes.set_xlabel("na koju reč gleda")
    axes.set_ylabel("reč koja pita")
    axes.add_patch(plt.Rectangle((-0.5, 4.5), 1, 1, fill=False,
                                 edgecolor=ORANGE, lw=3))
    axes.add_patch(plt.Rectangle((-0.5, 6.5), 1, 1, fill=False,
                                 edgecolor=ORANGE, lw=3))
    figure.colorbar(image, ax=axes, fraction=0.046, label="težina pažnje")
    save_figure(figure, "attention_heatmap")


def figure_transformer_block() -> None:
    figure, axes = create_blank_canvas((8, 7.5))
    draw_box(axes, (0, -4.2), "Mačka  nije  pojela  ribu ...", MUTED_INK,
             5.4, 0.8)
    draw_box(axes, (0, -2.9), "reči → vektori", AQUA, 4.0, 0.8)
    axes.add_patch(FancyBboxPatch((-2.9, -1.85), 5.8, 3.4,
                                  boxstyle="round,pad=0.1",
                                  facecolor="#eef3fb", edgecolor=BLUE,
                                  lw=2))
    draw_box(axes, (0, -1.0), "pažnja: ko je važan?", BLUE, 4.4, 0.9)
    draw_box(axes, (0, 0.6), "obrada svake reči", VIOLET, 4.4, 0.9)
    axes.text(3.25, -0.2, "× 100", fontsize=22, color=BLUE,
              fontweight="bold", va="center")
    draw_box(axes, (0, 2.6), "verovatnoće sledeće reči", ORANGE, 4.8, 0.9)
    draw_arrow(axes, (0, -3.8), (0, -3.3))
    draw_arrow(axes, (0, -2.5), (0, -1.5))
    draw_arrow(axes, (0, -0.55), (0, 0.15))
    draw_arrow(axes, (0, 1.05), (0, 2.15))
    axes.set_xlim(-4, 4.6)
    axes.set_ylim(-4.8, 3.4)
    save_figure(figure, "transformer_block")


def figure_alphafold_pipeline() -> None:
    figure, axes = create_blank_canvas((12, 3.8))
    draw_chain(
        axes,
        [
            ("MKTAYIAK...", MUTED_INK),
            ("slične sekvence\nu evoluciji", AQUA),
            ("pažnja nad\nparovima", BLUE),
            ("3D struktura", ORANGE),
        ],
        spacing=3.2,
        width=2.6,
        height=1.3,
    )
    axes.text(-4.8, -1.2, "aminokiseline", ha="center", fontsize=13,
              color=MUTED_INK)
    axes.text(1.6, -1.2, "Evoformer (Transformer)", ha="center",
              fontsize=13, color=MUTED_INK)
    axes.set_xlim(-6.3, 6.3)
    axes.set_ylim(-1.7, 1.2)
    save_figure(figure, "alphafold_pipeline")


def figure_contact_map() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    length = 80
    t = np.linspace(0, 6 * math.pi, length)
    coordinates = np.stack(
        [np.cos(t) * (1 + 0.3 * np.sin(t / 3)),
         np.sin(t) * (1 + 0.3 * np.sin(t / 3)),
         t / 4 * np.sin(t / 6)],
        axis=1,
    ) * 4
    coordinates += generator.normal(0, 0.25, size=coordinates.shape)
    distances = np.linalg.norm(
        coordinates[:, None, :] - coordinates[None, :, :], axis=-1
    )
    figure = plt.figure(figsize=FIGURE_SIZE_WIDE)
    chain = figure.add_subplot(1, 2, 1, projection="3d")
    chain.plot(*coordinates.T, color=BLUE, lw=2.5)
    chain.scatter(*coordinates.T, c=np.arange(length), cmap="Oranges", s=18)
    chain.set_axis_off()
    chain.set_title("struktura")
    contact = figure.add_subplot(1, 2, 2)
    contact.grid(False)
    contact.imshow(distances < 4.5, cmap="Blues")
    contact.set_title("koji parovi su blizu")
    contact.set_xlabel("aminokiselina $j$")
    contact.set_ylabel("aminokiselina $i$")
    save_figure(figure, "contact_map")


def figure_universal_approximation() -> None:
    x = np.linspace(0, 1, 800)
    target = np.sin(2 * math.pi * x) + 0.4 * np.sin(7 * math.pi * x)
    pieces = [3, 8, 30]
    colors = [AQUA, BLUE, ORANGE]
    figure, axes_row = plt.subplots(1, 3, figsize=(12, 3.9), sharey=True)
    for axes, count, color in zip(axes_row, pieces, colors):
        knots = np.linspace(0, 1, count + 1)
        values = (
            np.sin(2 * math.pi * knots) + 0.4 * np.sin(7 * math.pi * knots)
        )
        axes.plot(x, target, color=GRID, lw=5)
        axes.plot(knots, values, color=color, lw=2.2)
        axes.set_title(f"{count} neurona")
        axes.set_xticks([])
    axes_row[0].set_yticks([])
    save_figure(figure, "universal_approximation")


def polynomial_features(x: np.ndarray, degree: int) -> np.ndarray:
    return np.vander(x, degree + 1, increasing=True)


def fit_polynomial(x, y, degree, regularization=1e-8) -> np.ndarray:
    features = polynomial_features(x, degree)
    identity = np.eye(degree + 1)
    return np.linalg.solve(
        features.T @ features + regularization * identity, features.T @ y
    )


def true_function(x: np.ndarray) -> np.ndarray:
    return np.sin(2 * math.pi * x)


def sample_training_set(generator, size: int = 15, noise: float = 0.3):
    x = np.sort(generator.uniform(0, 1, size=size))
    return x, true_function(x) + generator.normal(0, noise, size=size)


def figure_bias_variance_fits() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    grid = np.linspace(0, 1, 300)
    cases = [(1, "premali: pristrasnost"), (3, "taman"),
             (12, "preveliki: varijansa")]
    figure, axes_row = plt.subplots(1, 3, figsize=(12, 4.2), sharey=True)
    for axes, (degree, title) in zip(axes_row, cases):
        for _ in range(20):
            x, y = sample_training_set(generator)
            coefficients = fit_polynomial(x, y, degree)
            axes.plot(grid, polynomial_features(grid, degree) @ coefficients,
                      color=BLUE, alpha=0.25, lw=1.5)
        axes.plot(grid, true_function(grid), color=ORANGE, lw=3)
        axes.set_ylim(-2, 2)
        axes.set_title(f"stepen {degree} — {title}", fontsize=15)
        axes.set_xticks([])
    save_figure(figure, "bias_variance_fits")


class BiasVarianceExperiment:
    def __init__(self, repetitions: int, seed: int) -> None:
        self.repetitions = repetitions
        self.generator = np.random.default_rng(seed)
        self.grid = np.linspace(0.05, 0.95, 100)

    def decompose(self, degree: int) -> tuple[float, float]:
        predictions = np.array([
            polynomial_features(self.grid, degree)
            @ fit_polynomial(*sample_training_set(self.generator), degree,
                             regularization=1e-4)
            for _ in range(self.repetitions)
        ])
        mean_prediction = predictions.mean(axis=0)
        bias = np.mean((mean_prediction - true_function(self.grid)) ** 2)
        variance = np.mean(predictions.var(axis=0))
        return float(bias), float(variance)


def figure_bias_variance_curve() -> None:
    experiment = BiasVarianceExperiment(BIAS_VARIANCE_REPETITIONS, RANDOM_SEED)
    degrees = np.arange(0, 11)
    results = np.array([experiment.decompose(int(d)) for d in degrees])
    noise = 0.3 ** 2
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    axes.plot(degrees, results[:, 0], "o-", color=BLUE,
              label="pristrasnost²")
    axes.plot(degrees, results[:, 1], "o-", color=ORANGE, label="varijansa")
    total = results.sum(axis=1) + noise
    axes.plot(degrees, total, "o-", color=INK, lw=3, label="ukupna greška")
    axes.axhline(noise, color=MUTED_INK, ls="--", label="šum")
    best = int(degrees[np.argmin(total)])
    axes.annotate("najbolji model", xy=(best, total.min()),
                  xytext=(best + 1.5, 0.025), fontsize=15,
                  arrowprops={"arrowstyle": "->", "color": INK})
    axes.set_yscale("log")
    axes.set_xlabel("složenost modela (stepen polinoma)")
    axes.set_ylabel("greška")
    axes.legend(loc="lower left", ncol=2)
    save_figure(figure, "bias_variance_curve")


def figure_generalization() -> None:
    generator = np.random.default_rng(RANDOM_SEED)
    x_train, y_train = sample_training_set(generator, size=12)
    x_test, y_test = sample_training_set(generator, size=200)
    degrees = np.arange(0, 12)
    train_errors, test_errors = [], []
    for degree in degrees:
        coefficients = fit_polynomial(x_train, y_train, int(degree))
        train_errors.append(np.mean(
            (polynomial_features(x_train, int(degree)) @ coefficients
             - y_train) ** 2))
        test_errors.append(np.mean(
            (polynomial_features(x_test, int(degree)) @ coefficients
             - y_test) ** 2))
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    axes.plot(degrees, np.maximum(train_errors, 1e-4), "o-", color=BLUE,
              label="trening (viđeni podaci)")
    axes.plot(degrees, test_errors, "o-", color=ORANGE,
              label="test (novi podaci)")
    axes.axvspan(8.5, 11.5, color=RED, alpha=0.08)
    axes.text(10, 0.08, "bubanje", ha="center", fontsize=16, color=RED)
    axes.set_yscale("log")
    axes.set_xlabel("složenost modela")
    axes.set_ylabel("greška")
    axes.legend(loc="lower left")
    save_figure(figure, "generalization")


def figure_training_pipeline() -> None:
    figure, axes = create_blank_canvas((12, 3.8))
    centers = draw_chain(
        axes,
        [
            ("pred-trening", BLUE),
            ("fino\npodešavanje", VIOLET),
            ("učenje iz\npovratne veze", ORANGE),
            ("asistent", GREEN),
        ],
        spacing=3.3,
        width=2.6,
        height=1.3,
    )
    captions = [
        "ceo internet\n„predvidi sledeću reč”",
        "primeri razgovora\nkoje pišu ljudi",
        "ljudi i testovi\nocenjuju odgovore",
        "",
    ]
    for (x, _), caption in zip(centers, captions):
        axes.text(x, -1.1, caption, ha="center", va="top", fontsize=13,
                  color=MUTED_INK)
    axes.set_xlim(-6.6, 6.6)
    axes.set_ylim(-2.4, 1.1)
    save_figure(figure, "training_pipeline")


@dataclass(frozen=True)
class TrainedModel:
    name: str
    year: int
    parameters: float
    tokens: float

    def training_compute(self) -> float:
        return 6 * self.parameters * self.tokens


PUBLISHED_MODELS = [
    TrainedModel("GPT-3", 2020, 175e9, 300e9),
    TrainedModel("PaLM", 2022, 540e9, 780e9),
    TrainedModel("Chinchilla", 2022, 70e9, 1.4e12),
    TrainedModel("Llama 2", 2023, 70e9, 2e12),
    TrainedModel("Llama 3.1", 2024, 405e9, 15.6e12),
]


def figure_training_compute() -> None:
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    years = [model.year for model in PUBLISHED_MODELS]
    compute = [model.training_compute() for model in PUBLISHED_MODELS]
    axes.scatter(years, compute, s=120, color=BLUE, zorder=3)
    offsets = {"PaLM": (-0.1, 2.2), "Chinchilla": (0.1, 0.35)}
    for model, value in zip(PUBLISHED_MODELS, compute):
        dx, factor = offsets.get(model.name, (0.12, 1.6))
        axes.text(model.year + dx, value * factor, model.name, fontsize=14,
                  ha="right" if dx < 0 else "left")
    axes.set_yscale("log")
    axes.set_xlim(2019.5, 2025.3)
    axes.set_ylim(1e23, 1e26)
    axes.set_xlabel("godina")
    axes.set_ylabel("računanje $6ND$ (FLOP)")
    axes.set_title("GPT-3 → Llama 3.1: ~100× više računanja za 4 godine")
    save_figure(figure, "training_compute")


def figure_compression() -> None:
    items = [
        ("tekst za trening\n15.6T tokena", 60e12, MUTED_INK),
        ("model\n405B parametara", 0.81e12, BLUE),
        ("Vikipedija\n(engleska, ≈ tekst)", 0.02e12, AQUA),
    ]
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    labels = [label for label, _, _ in items]
    sizes = [size / 1e9 for _, size, _ in items]
    axes.bar(labels, sizes, color=[c for _, _, c in items], width=0.55)
    for index, size in enumerate(sizes):
        text = f"{size / 1000:.0f} TB" if size >= 1000 else f"{size:.0f} GB"
        axes.text(index, size * 1.3, text, ha="center", fontsize=16)
    axes.set_yscale("log")
    axes.set_ylim(5, 5e5)
    axes.set_ylabel("veličina (GB)")
    axes.set_title("model je ~75× manji od teksta iz kojeg je učio")
    axes.grid(axis="x", visible=False)
    save_figure(figure, "compression")


def figure_dpi_chain() -> None:
    figure, axes = create_blank_canvas((12, 4.6))
    steps = [("Svet", GREEN, 3.0), ("Ljudi", BLUE, 2.2),
             ("Tekst", VIOLET, 1.5), ("Model", ORANGE, 0.9)]
    spacing = 3.4
    offset = spacing * (len(steps) - 1) / 2
    for index, (label, color, height) in enumerate(steps):
        x = index * spacing - offset
        axes.add_patch(FancyBboxPatch((x - 1.0, -height / 2), 2.0, height,
                                      boxstyle="round,pad=0.05",
                                      facecolor=color, edgecolor="none"))
        axes.text(x, 0, label, ha="center", va="center", color="white",
                  fontsize=18, fontweight="bold")
        if index < len(steps) - 1:
            draw_arrow(axes, (x + 1.1, 0), (x + spacing - 1.1, 0))
        else:
            continue
    captions = ["opažanje", "zapisivanje", "kompresija"]
    for index, caption in enumerate(captions):
        x = index * spacing - offset + spacing / 2
        axes.text(x, 0.35, caption, ha="center", fontsize=13,
                  color=MUTED_INK)
    axes.text(0, -2.1, "visina = koliko informacije o svetu ostaje",
              ha="center", fontsize=14, color=MUTED_INK)
    axes.set_xlim(-6.6, 6.6)
    axes.set_ylim(-2.5, 1.9)
    save_figure(figure, "dpi_chain")


def figure_agent_loop() -> None:
    figure, axes = create_blank_canvas((10, 5.6))
    draw_box(axes, (-3, 0), "LLM\n(mozak)", BLUE, 2.6, 1.4)
    draw_box(axes, (3, 1.6), "alati\nkod · pretraga · Lean", VIOLET, 3.4, 1.3)
    draw_box(axes, (3, -1.6), "okruženje\nrezultat · greška", AQUA, 3.4, 1.3)
    draw_box(axes, (-3, 2.9), "cilj", ORANGE, 1.8, 0.8)
    draw_arrow(axes, (-3, 2.45), (-3, 0.75))
    draw_arrow(axes, (-1.65, 0.5), (1.25, 1.5), curve=-0.2)
    draw_arrow(axes, (3, 0.9), (3, -0.9))
    draw_arrow(axes, (1.25, -1.5), (-1.65, -0.5), curve=-0.2)
    axes.text(-0.4, 1.75, "akcija", fontsize=15, ha="center", color=INK)
    axes.text(-0.4, -1.85, "opažanje", fontsize=15, ha="center", color=INK)
    axes.text(0, -3.3, "povratna sprega: probaj → vidi → ispravi",
              ha="center", fontsize=16, color=MUTED_INK)
    axes.set_xlim(-5, 5.2)
    axes.set_ylim(-3.7, 3.5)
    save_figure(figure, "agent_loop")


def figure_error_compounding() -> None:
    steps = np.arange(0, 101)
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    for probability, color in [(0.9, RED), (0.99, ORANGE)]:
        axes.plot(steps, probability ** steps, color=color,
                  label=f"$p = {probability}$ po koraku")
    retries = 3
    verified = (1 - (1 - 0.9) ** retries) ** steps
    axes.plot(steps, verified, color=GREEN, lw=3, ls="--",
              label="$p = 0.9$ + provera, 3 pokušaja $\\Rightarrow 0.999$")
    axes.set_xlabel("broj koraka $n$")
    axes.set_ylabel("P(sve tačno) $= p^n$")
    axes.set_ylim(0, 1.02)
    axes.legend(loc="lower right", bbox_to_anchor=(1, 0.06))
    save_figure(figure, "error_compounding")


def figure_navier_stokes_terms() -> None:
    figure, axes = create_blank_canvas((12, 3.4))
    terms = [
        (-5.0, "$\\frac{\\partial u}{\\partial t}$", "promena\nbrzine", BLUE),
        (-3.2, "$+$", "", INK),
        (-1.9, "$(u \\cdot \\nabla) u$", "tok nosi\nsam sebe", VIOLET),
        (-0.4, "$=$", "", INK),
        (0.8, "$-\\nabla p$", "pritisak", AQUA),
        (2.0, "$+$", "", INK),
        (3.1, "$\\nu \\Delta u$", "trenje\n(viskoznost)", ORANGE),
        (4.2, "$+$", "", INK),
        (5.1, "$f$", "spoljna\nsila", RED),
    ]
    for x, formula, caption, color in terms:
        axes.text(x, 0.4, formula, ha="center", va="center", fontsize=34,
                  color=color)
        if caption:
            axes.text(x, -1.0, caption, ha="center", va="top", fontsize=14,
                      color=color)
        else:
            continue
    axes.set_xlim(-6, 6)
    axes.set_ylim(-2.2, 1.4)
    save_figure(figure, "navier_stokes_terms")


def figure_blowup() -> None:
    time = np.linspace(0, 0.995, 400)
    blowup_time = 1.0
    figure, axes = plt.subplots(figsize=FIGURE_SIZE_WIDE)
    smooth = 1 + 0.6 * np.sin(4 * time) * np.exp(-time)
    axes.plot(time * 1.2, smooth, color=BLUE,
              label="glatko rešenje: ostaje konačno")
    exploding = 1 / (blowup_time - time) ** 0.5
    axes.plot(time, exploding, color=RED,
              label="eksplozija: $|u| \\to \\infty$")
    axes.axvline(blowup_time, color=RED, ls="--")
    axes.text(blowup_time + 0.01, 9, "$T^*$", fontsize=20, color=RED)
    axes.set_ylim(0, 12)
    axes.set_xlim(0, 1.2)
    axes.set_xlabel("vreme $t$")
    axes.set_ylabel("najveća brzina $\\max|u|$")
    axes.legend(loc="upper left")
    save_figure(figure, "blowup")


def figure_lean_feedback() -> None:
    figure, axes = create_blank_canvas((11, 5))
    draw_box(axes, (-3.8, 0), "AI agenti\npredlažu dokaz", BLUE, 3.0, 1.4)
    draw_box(axes, (0.6, 0), "Lean jezgro\nproverava svaki korak", MUTED_INK,
             3.4, 1.4)
    draw_box(axes, (4.4, 1.3), "✓ dokazano", GREEN, 2.4, 0.9)
    draw_box(axes, (4.4, -1.3), "✗ greška u koraku", RED, 2.8, 0.9)
    draw_arrow(axes, (-2.25, 0), (-1.15, 0))
    draw_arrow(axes, (2.35, 0.3), (3.15, 1.1))
    draw_arrow(axes, (2.35, -0.3), (3.0, -1.1))
    draw_arrow(axes, (3.0, -1.75), (-3.8, -0.75), color=RED, curve=-0.35)
    axes.text(-0.6, -2.9, "poruka o grešci nazad agentu", ha="center",
              fontsize=14, color=RED)
    axes.set_xlim(-5.5, 6)
    axes.set_ylim(-3.4, 2.2)
    save_figure(figure, "lean_feedback")


def figure_navier_stokes_timeline() -> None:
    events = [
        (0, "15. avg", "Buckmaster i Alpöge:\neksplozija forsiranog Ojlera",
         AQUA),
        (7, "22. avg", "njihov dokaz\nproveren u Lean-u", VIOLET),
        (17, "1. sep", "OpenAI počinje:\n~10.000 agenata", BLUE),
        (21, "+88 h", "rezultat, pa\n+17 h Lean", ORANGE),
        (24, "8. sep", "objava: forsirani\nNavier–Stokes", RED),
    ]
    figure, axes = create_blank_canvas((12, 3.6))
    axes.plot([-2, 26], [0, 0], color=INK, lw=2)
    for index, (day, date, label, color) in enumerate(events):
        side = 1 if index % 2 == 0 else -1
        axes.scatter(day, 0, s=180, color=color, zorder=3)
        axes.plot([day, day], [0, 0.5 * side], color=color)
        axes.text(day, 0.62 * side, label, ha="center",
                  va="bottom" if side > 0 else "top", fontsize=13)
        axes.text(day, -0.28 * side, date, ha="center",
                  va="top" if side > 0 else "bottom", fontsize=13,
                  color=MUTED_INK)
    axes.set_xlim(-4, 28)
    axes.set_ylim(-2, 2)
    save_figure(figure, "navier_stokes_timeline")


def figure_turing_test() -> None:
    figure, axes = create_blank_canvas((10, 5))
    draw_box(axes, (-3.5, 0), "sudija", ORANGE, 2.2, 1.0)
    draw_box(axes, (3.2, 1.5), "čovek", GREEN, 2.2, 1.0)
    draw_box(axes, (3.2, -1.5), "mašina", BLUE, 2.2, 1.0)
    axes.plot([0.6, 0.6], [-2.6, 2.6], color=MUTED_INK, lw=6)
    axes.text(0.6, 2.9, "zid", ha="center", fontsize=14, color=MUTED_INK)
    draw_arrow(axes, (-2.3, 0.3), (2.0, 1.4), curve=-0.1)
    draw_arrow(axes, (-2.3, -0.3), (2.0, -1.4), curve=0.1)
    axes.text(-0.4, 1.4, "pitanja", fontsize=14, ha="center")
    axes.text(-3.5, -1.3, "Ko je ko?", fontsize=18, ha="center",
              color=INK)
    axes.set_xlim(-5, 4.8)
    axes.set_ylim(-3, 3.3)
    save_figure(figure, "turing_test")


def figure_formal_system() -> None:
    figure, axes = create_blank_canvas((11, 5))
    draw_box(axes, (-4.2, 1.5), "aksiome", BLUE, 2.2, 0.9)
    draw_box(axes, (-4.2, 0), "pravila", VIOLET, 2.2, 0.9)
    draw_box(axes, (-4.2, -1.5), "simboli", AQUA, 2.2, 0.9)
    draw_arrow(axes, (-3.0, 1.2), (-0.6, 0.3))
    draw_arrow(axes, (-3.0, 0), (-0.6, 0))
    draw_arrow(axes, (-3.0, -1.2), (-0.6, -0.3))
    axes.add_patch(Circle((2.6, 0), 2.6, facecolor="#fde7dd",
                          edgecolor=ORANGE, lw=2))
    axes.add_patch(Circle((2.0, 0), 1.6, facecolor="#dbe8f8",
                          edgecolor=BLUE, lw=2))
    axes.text(2.0, 0, "dokazive\nteoreme", ha="center", va="center",
              fontsize=15, color=INK)
    axes.text(4.35, 0.15, "istinite,\nali\nnedokazive", ha="center",
              va="center", fontsize=12, color=ORANGE)
    axes.text(2.6, 2.85, "sve istinite tvrdnje", ha="center", fontsize=14,
              color=ORANGE)
    axes.text(-4.2, -2.7, "Gedel (1931)", ha="center", fontsize=15,
              color=MUTED_INK)
    axes.set_xlim(-5.6, 5.6)
    axes.set_ylim(-3.0, 3.3)
    axes.set_aspect("equal")
    save_figure(figure, "formal_system")


def figure_summary_chain() -> None:
    figure, axes = create_blank_canvas((13, 2.8))
    draw_chain(
        axes,
        [
            ("model", MUTED_INK),
            ("mašinsko\nučenje", AQUA),
            ("jezički\nmodel", BLUE),
            ("LLM", VIOLET),
            ("agent +\nverifikator", ORANGE),
        ],
        spacing=2.8,
        width=2.2,
        height=1.2,
    )
    axes.set_xlim(-6.8, 6.8)
    axes.set_ylim(-1, 1)
    save_figure(figure, "summary_chain")


@dataclass(frozen=True)
class FigureSpecification:
    name: str
    render: Callable[[], None]


FIGURE_REGISTRY = [
    FigureSpecification("model_map", figure_model_map),
    FigureSpecification("model_spectrum", figure_model_spectrum),
    FigureSpecification("programming_vs_learning",
                        figure_programming_vs_learning),
    FigureSpecification("fitting_loss", figure_fitting_loss),
    FigureSpecification("neural_network", figure_neural_network),
    FigureSpecification("next_token", figure_next_token),
    FigureSpecification("language_model_timeline",
                        figure_language_model_timeline),
    FigureSpecification("scaling_law", figure_scaling_law),
    FigureSpecification("attention_heatmap", figure_attention_heatmap),
    FigureSpecification("transformer_block", figure_transformer_block),
    FigureSpecification("alphafold_pipeline", figure_alphafold_pipeline),
    FigureSpecification("contact_map", figure_contact_map),
    FigureSpecification("universal_approximation",
                        figure_universal_approximation),
    FigureSpecification("generalization", figure_generalization),
    FigureSpecification("bias_variance_fits", figure_bias_variance_fits),
    FigureSpecification("bias_variance_curve", figure_bias_variance_curve),
    FigureSpecification("training_pipeline", figure_training_pipeline),
    FigureSpecification("training_compute", figure_training_compute),
    FigureSpecification("compression", figure_compression),
    FigureSpecification("dpi_chain", figure_dpi_chain),
    FigureSpecification("agent_loop", figure_agent_loop),
    FigureSpecification("error_compounding", figure_error_compounding),
    FigureSpecification("navier_stokes_terms", figure_navier_stokes_terms),
    FigureSpecification("blowup", figure_blowup),
    FigureSpecification("lean_feedback", figure_lean_feedback),
    FigureSpecification("navier_stokes_timeline",
                        figure_navier_stokes_timeline),
    FigureSpecification("turing_test", figure_turing_test),
    FigureSpecification("formal_system", figure_formal_system),
    FigureSpecification("summary_chain", figure_summary_chain),
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
