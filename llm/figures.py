from __future__ import annotations

import math
import sys
from dataclasses import dataclass
from pathlib import Path

import matplotlib

matplotlib.use("Agg")

import matplotlib.pyplot as plt
import numpy as np

REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
if str(REPOSITORY_ROOT) not in sys.path:
    sys.path.insert(0, str(REPOSITORY_ROOT))

from figures_framework.diagrams import (
    DiagramNode,
    EquationTermsDiagram,
    FeedbackLoopDiagram,
    FlowDiagram,
    FunnelDiagram,
    LayeredNetworkDiagram,
    LayeredStackDiagram,
    MergeFlowDiagram,
    NestedSetsDiagram,
    RepeatedGroup,
    SpectrumDiagram,
    StackedDiagrams,
    TimelineDiagram,
    VerificationLoopDiagram,
)
from figures_framework import (
    DEFAULT_DIAGRAM_SIZE,
    DEFAULT_WIDE_SIZE,
    BoxSize,
    FigureContext,
    FigureRegistry,
    GridSpecification,
    TimelineEvent,
    environment_integer,
    fit_polynomial,
    polynomial_features,
    render_registry,
)

FIGURES = FigureRegistry("llm")
DEFAULT_OUTPUT_DIRECTORY = Path(__file__).parent / "img"
DEFAULT_SEED = 7
OVERFIT_BAND_COLOR = "#fdecea"
BIAS_VARIANCE_REPETITIONS = environment_integer(
    "BIAS_VARIANCE_REPETITIONS", 300
)


@FIGURES.register("model_map")
def render_model_map(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    canvas = context.blank_canvas(DEFAULT_DIAGRAM_SIZE)
    axes = canvas.axes
    cloud = generator.normal([-4, 0], [0.7, 0.9], size=(160, 2))
    axes.scatter(
        cloud[:, 0],
        cloud[:, 1],
        s=14,
        color=palette.muted_ink,
        alpha=0.6,
    )
    axes.text(-4, 2.3, "Svet", ha="center", fontsize=20, color=palette.ink)
    axes.text(-4, -2.4, "složen, pun šuma", ha="center", fontsize=14,
              color=palette.muted_ink)
    canvas.draw_arrow((-2.6, 0), (-1.3, 0))
    canvas.draw_box(
        (0, 0),
        "Model\n$y = f(x)$",
        palette.blue,
        BoxSize(2.4, 1.4),
    )
    axes.text(0, -1.4, "uprošćenje", ha="center", fontsize=14,
              color=palette.muted_ink)
    canvas.draw_arrow((1.3, 0), (2.6, 0))
    canvas.draw_box((4, 0), "Predikcija", palette.orange, BoxSize(2.4, 1.0))
    canvas.draw_arrow((4, -0.7), (-4, -1.4), color=palette.aqua, curve=-0.35)
    axes.text(0, -3.0, "proveravamo eksperimentom", ha="center",
              fontsize=14, color=palette.aqua)
    axes.set_xlim(-5.6, 5.6)
    axes.set_ylim(-3.4, 2.9)
    return canvas.figure


@FIGURES.register("model_spectrum")
def render_model_spectrum(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return SpectrumDiagram(
        marks=[
            DiagramNode("$F = ma$", palette.ink, "Njutn"),
            DiagramNode("$y = ax + b$", palette.ink, "regresija"),
            DiagramNode("stablo\nodlučivanja", palette.ink, "ML"),
            DiagramNode("neuronska\nmreža", palette.ink, "duboko učenje"),
            DiagramNode("LLM", palette.ink, "$10^{11}$ parametara"),
        ],
        ends=(
            "BELA KUTIJA: razumemo svaki deo",
            "CRNA KUTIJA: radi, ali ne znamo zašto",
        ),
    ).render(context)


@FIGURES.register("programming_vs_learning")
def render_programming_vs_learning(context: FigureContext) -> plt.Figure:
    palette = context.palette
    classical = MergeFlowDiagram(
        inputs=[
            DiagramNode("pravila", palette.blue),
            DiagramNode("podaci", palette.aqua),
        ],
        process=DiagramNode("program", palette.muted_ink),
        output=DiagramNode("odgovori", palette.orange),
    )
    learned = MergeFlowDiagram(
        inputs=[
            DiagramNode("podaci", palette.aqua),
            DiagramNode("odgovori", palette.orange),
        ],
        process=DiagramNode("učenje", palette.muted_ink),
        output=DiagramNode("pravila", palette.blue),
    )
    return StackedDiagrams(
        rows=[
            ("Klasično\nprogramiranje", classical),
            ("Mašinsko\nučenje", learned),
        ]
    ).render(context)


@FIGURES.register("fitting_loss")
def render_fitting_loss(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    x = np.linspace(0, 10, 25)
    y = 0.8 * x + 1 + generator.normal(0, 1.2, size=x.size)
    slope = 0.8
    figure, (fit, loss) = context.create_figure(
        DEFAULT_WIDE_SIZE, GridSpecification(1, 2)
    )
    prediction = slope * x + 1
    for xi, yi, pi in zip(x, y, prediction):
        fit.plot([xi, xi], [yi, pi], color=palette.orange, lw=1.5)
    fit.scatter(x, y, color=palette.blue, s=30, zorder=3)
    fit.plot(x, prediction, color=palette.ink)
    fit.set_title("greška = rastojanje do prave")
    fit.set_xlabel("$x$")
    fit.set_ylabel("$y$")
    slopes = np.linspace(-0.2, 1.8, 200)
    losses = [np.mean((y - (s * x + 1)) ** 2) for s in slopes]
    loss.plot(slopes, losses, color=palette.ink)
    current = -0.1
    for _ in range(6):
        gradient = np.mean(-2 * x * (y - (current * x + 1)))
        value = np.mean((y - (current * x + 1)) ** 2)
        loss.scatter(current, value, color=palette.orange, s=60, zorder=3)
        next_value = current - 0.006 * gradient
        next_loss = np.mean((y - (next_value * x + 1)) ** 2)
        loss.annotate("", xy=(next_value, next_loss), xytext=(current, value),
                      arrowprops={"arrowstyle": "->", "color": palette.orange})
        current = next_value
    loss.set_title("učenje = spuštanje niz grešku")
    loss.set_xlabel("parametar $a$")
    loss.set_ylabel("greška $L(a)$")
    return figure


@FIGURES.register("neural_network")
def render_neural_network(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return LayeredNetworkDiagram(
        layer_sizes=[3, 5, 5, 2],
        layer_colors=[palette.aqua, palette.blue, palette.blue,
                      palette.orange],
        layer_labels=["ulaz", "skriveni slojevi", "", "izlaz"],
        note="neuron: $y = \\max(0,\\ w_1 x_1 + w_2 x_2 + b)$",
    ).render(context)


@FIGURES.register("next_token")
def render_next_token(context: FigureContext) -> plt.Figure:
    palette = context.palette
    candidates = [
        ("Valjeva", 0.71), ("Beograda", 0.08), ("reke", 0.06),
        ("Novog Sada", 0.03), ("mora", 0.01),
    ]
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    words = [word for word, _ in candidates][::-1]
    probabilities = [p for _, p in candidates][::-1]
    colors = [palette.muted_ink] * (len(words) - 1) + [palette.orange]
    axes.barh(words, probabilities, color=colors, height=0.6)
    for index, probability in enumerate(probabilities):
        axes.text(probability + 0.01, index, f"{probability:.2f}",
                  va="center", fontsize=15)
    axes.set_title("„Petnica se nalazi pored ___”", fontsize=20)
    axes.set_xlabel("$P(\\mathrm{reč} \\mid \\mathrm{prethodne\\ reči})$")
    axes.set_xlim(0, 0.85)
    axes.grid(axis="y", visible=False)
    return figure


@FIGURES.register("language_model_timeline")
def render_language_model_timeline(context: FigureContext) -> plt.Figure:
    palette = context.palette
    events = [
        (1948, "Šenon:\nn-grami", palette.blue),
        (1966, "ELIZA", palette.muted_ink),
        (1997, "LSTM", palette.violet),
        (2013, "word2vec", palette.aqua),
        (2017, "Transformer", palette.orange),
        (2020, "GPT-3", palette.red),
        (2022, "ChatGPT", palette.green),
        (2026, "agenti", palette.yellow),
    ]
    return TimelineDiagram(
        events=[
            TimelineEvent(label=label, caption=str(year), color=color)
            for year, label, color in events
        ]
    ).render(context)


def scaling_loss(compute: np.ndarray, parameters: float) -> np.ndarray:
    capacity_term = 400 / parameters ** 0.34
    data_term = 2.6e3 / (compute / (6 * parameters)) ** 0.28
    return 1.7 + capacity_term + data_term


@FIGURES.register("scaling_law")
def render_scaling_law(context: FigureContext) -> plt.Figure:
    palette = context.palette
    compute = np.logspace(18, 26, 200)
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    sizes = [
        (1e8, palette.aqua, "$10^8$"),
        (1e9, palette.blue, "$10^9$"),
        (1e10, palette.violet, "$10^{10}$"),
        (1e11, palette.orange, "$10^{11}$"),
    ]
    for parameters, color, label in sizes:
        loss = scaling_loss(compute, parameters)
        start = compute >= 6 * parameters * 2e8
        axes.plot(compute[start], loss[start], color=color,
                  label=f"$N = ${label}")
    envelope = np.min(
        [scaling_loss(compute, n) for n in np.logspace(7, 13, 120)], axis=0
    )
    axes.plot(compute, envelope, color=palette.ink, ls="--", lw=3,
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
    return figure


@FIGURES.register("attention_heatmap")
def render_attention_heatmap(context: FigureContext) -> plt.Figure:
    palette = context.palette
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
    figure, axes = context.create_figure((7.4, 6.4))
    axes.grid(False)
    image = axes.imshow(weights, cmap="Blues", vmin=0, vmax=0.8)
    axes.set_xticks(range(size), tokens, rotation=45, ha="right")
    axes.set_yticks(range(size), tokens)
    axes.set_xlabel("na koju reč gleda")
    axes.set_ylabel("reč koja pita")
    axes.add_patch(plt.Rectangle((-0.5, 4.5), 1, 1, fill=False,
                                 edgecolor=palette.orange, lw=3))
    axes.add_patch(plt.Rectangle((-0.5, 6.5), 1, 1, fill=False,
                                 edgecolor=palette.orange, lw=3))
    figure.colorbar(image, ax=axes, fraction=0.046, label="težina pažnje")
    return figure


@FIGURES.register("transformer_block")
def render_transformer_block(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return LayeredStackDiagram(
        layers=[
            DiagramNode("Mačka  nije  pojela  ribu ...", palette.muted_ink),
            DiagramNode("reči → vektori", palette.aqua),
            DiagramNode("pažnja: ko je važan?", palette.blue),
            DiagramNode("obrada svake reči", palette.violet),
            DiagramNode("verovatnoće sledeće reči", palette.orange),
        ],
        repeated=RepeatedGroup(first=2, last=3, label="× 100"),
    ).render(context)


@FIGURES.register("alphafold_pipeline")
def render_alphafold_pipeline(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return FlowDiagram(
        steps=[
            DiagramNode("MKTAYIAK...", palette.muted_ink, "aminokiseline"),
            DiagramNode("slične sekvence\nu evoluciji", palette.aqua),
            DiagramNode("pažnja nad\nparovima", palette.blue,
                        "Evoformer (Transformer)"),
            DiagramNode("3D struktura", palette.orange),
        ],
        box_size=BoxSize(2.6, 1.3),
        spacing=3.2,
    ).render(context)


@FIGURES.register("contact_map")
def render_contact_map(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
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
    figure = plt.figure(figsize=DEFAULT_WIDE_SIZE)
    chain = figure.add_subplot(1, 2, 1, projection="3d")
    chain.plot(*coordinates.T, color=palette.blue, lw=2.5)
    chain.scatter(*coordinates.T, c=np.arange(length), cmap="Oranges", s=18)
    chain.set_axis_off()
    chain.set_title("struktura")
    contact = figure.add_subplot(1, 2, 2)
    contact.grid(False)
    contact.imshow(distances < 4.5, cmap="Blues")
    contact.set_title("koji parovi su blizu")
    contact.set_xlabel("aminokiselina $j$")
    contact.set_ylabel("aminokiselina $i$")
    return figure


@FIGURES.register("universal_approximation")
def render_universal_approximation(context: FigureContext) -> plt.Figure:
    palette = context.palette
    x = np.linspace(0, 1, 800)
    target = np.sin(2 * math.pi * x) + 0.4 * np.sin(7 * math.pi * x)
    pieces = [3, 8, 30]
    colors = [palette.aqua, palette.blue, palette.orange]
    figure, axes_row = context.create_figure(
        (12, 3.9),
        GridSpecification(1, 3, shared_axis="y"),
    )
    for axes, count, color in zip(axes_row, pieces, colors):
        knots = np.linspace(0, 1, count + 1)
        values = (
            np.sin(2 * math.pi * knots) + 0.4 * np.sin(7 * math.pi * knots)
        )
        axes.plot(x, target, color=palette.grid, lw=5)
        axes.plot(knots, values, color=color, lw=2.2)
        axes.set_title(f"{count} neurona")
        axes.set_xticks([])
    axes_row[0].set_yticks([])
    return figure


def true_function(x: np.ndarray) -> np.ndarray:
    return np.sin(2 * math.pi * x)


def sample_training_set(generator, size: int = 15, noise: float = 0.3):
    x = np.sort(generator.uniform(0, 1, size=size))
    return x, true_function(x) + generator.normal(0, noise, size=size)


@FIGURES.register("bias_variance_fits")
def render_bias_variance_fits(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
    grid = np.linspace(0, 1, 300)
    cases = [(1, "premali: pristrasnost"), (3, "taman"),
             (12, "preveliki: varijansa")]
    figure, axes_row = context.create_figure(
        (12, 4.2),
        GridSpecification(1, 3, shared_axis="y"),
    )
    for axes, (degree, title) in zip(axes_row, cases):
        for _ in range(20):
            x, y = sample_training_set(generator)
            coefficients = fit_polynomial(x, y, degree)
            axes.plot(grid, polynomial_features(grid, degree) @ coefficients,
                      color=palette.blue, alpha=0.25, lw=1.5)
        axes.plot(grid, true_function(grid), color=palette.orange, lw=3)
        axes.set_ylim(-2, 2)
        axes.set_title(f"stepen {degree} — {title}", fontsize=15)
        axes.set_xticks([])
    return figure


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


@FIGURES.register("bias_variance_curve")
def render_bias_variance_curve(context: FigureContext) -> plt.Figure:
    palette = context.palette
    experiment = BiasVarianceExperiment(BIAS_VARIANCE_REPETITIONS, context.seed)
    degrees = np.arange(0, 11)
    results = np.array([experiment.decompose(int(d)) for d in degrees])
    noise = 0.3 ** 2
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    axes.plot(degrees, results[:, 0], "o-", color=palette.blue,
              label="pristrasnost²")
    axes.plot(
        degrees,
        results[:, 1],
        "o-",
        color=palette.orange,
        label="varijansa",
    )
    total = results.sum(axis=1) + noise
    axes.plot(
        degrees,
        total,
        "o-",
        color=palette.ink,
        lw=3,
        label="ukupna greška",
    )
    axes.axhline(noise, color=palette.muted_ink, ls="--", label="šum")
    best = int(degrees[np.argmin(total)])
    axes.annotate("najbolji model", xy=(best, total.min()),
                  xytext=(best + 1.5, 0.025), fontsize=15,
                  arrowprops={"arrowstyle": "->", "color": palette.ink})
    axes.set_yscale("log")
    axes.set_xlabel("složenost modela (stepen polinoma)")
    axes.set_ylabel("greška")
    axes.legend(loc="lower left", ncol=2)
    return figure


@FIGURES.register("generalization")
def render_generalization(context: FigureContext) -> plt.Figure:
    palette = context.palette
    generator = context.random
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
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    axes.plot(degrees, np.maximum(train_errors, 1e-4), "o-", color=palette.blue,
              label="trening (viđeni podaci)")
    axes.plot(degrees, test_errors, "o-", color=palette.orange,
              label="test (novi podaci)")
    axes.axvspan(8.5, 11.5, color=OVERFIT_BAND_COLOR)
    axes.text(10, 0.08, "bubanje", ha="center", fontsize=16, color=palette.red)
    axes.set_yscale("log")
    axes.set_xlabel("složenost modela")
    axes.set_ylabel("greška")
    axes.legend(loc="lower left")
    return figure


@FIGURES.register("training_pipeline")
def render_training_pipeline(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return FlowDiagram(
        steps=[
            DiagramNode("pred-trening", palette.blue,
                        "ceo internet\n„predvidi sledeću reč”"),
            DiagramNode("fino\npodešavanje", palette.violet,
                        "primeri razgovora\nkoje pišu ljudi"),
            DiagramNode("učenje iz\npovratne veze", palette.orange,
                        "ljudi i testovi\nocenjuju odgovore"),
            DiagramNode("asistent", palette.green),
        ],
        box_size=BoxSize(2.6, 1.3),
        spacing=3.3,
    ).render(context)


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


@FIGURES.register("training_compute")
def render_training_compute(context: FigureContext) -> plt.Figure:
    palette = context.palette
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    years = [model.year for model in PUBLISHED_MODELS]
    compute = [model.training_compute() for model in PUBLISHED_MODELS]
    axes.scatter(years, compute, s=120, color=palette.blue, zorder=3)
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
    return figure


@FIGURES.register("compression")
def render_compression(context: FigureContext) -> plt.Figure:
    palette = context.palette
    items = [
        ("tekst za trening\n15.6T tokena", 60e12, palette.muted_ink),
        ("model\n405B parametara", 0.81e12, palette.blue),
        ("Vikipedija\n(engleska, ≈ tekst)", 0.02e12, palette.aqua),
    ]
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
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
    return figure


@FIGURES.register("dpi_chain")
def render_dpi_chain(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return FunnelDiagram(
        steps=[
            DiagramNode("Svet", palette.green),
            DiagramNode("Ljudi", palette.blue),
            DiagramNode("Tekst", palette.violet),
            DiagramNode("Model", palette.orange),
        ],
        edge_captions=["opažanje", "zapisivanje", "kompresija"],
        note="visina = koliko informacije o svetu ostaje",
    ).render(context)


@FIGURES.register("agent_loop")
def render_agent_loop(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return FeedbackLoopDiagram(
        controller=DiagramNode("LLM\n(mozak)", palette.blue),
        upper=DiagramNode("alati\nkod · pretraga · Lean", palette.violet),
        lower=DiagramNode("okruženje\nrezultat · greška", palette.aqua),
        goal=DiagramNode("cilj", palette.orange),
        edge_labels=("akcija", "opažanje"),
        note="povratna sprega: probaj → vidi → ispravi",
    ).render(context)


@FIGURES.register("error_compounding")
def render_error_compounding(context: FigureContext) -> plt.Figure:
    palette = context.palette
    steps = np.arange(0, 101)
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    for probability, color in [(0.9, palette.red), (0.99, palette.orange)]:
        axes.plot(steps, probability ** steps, color=color,
                  label=f"$p = {probability}$ po koraku")
    retries = 3
    verified = (1 - (1 - 0.9) ** retries) ** steps
    axes.plot(steps, verified, color=palette.green, lw=3, ls="--",
              label="$p = 0.9$ + provera, 3 pokušaja $\\Rightarrow 0.999$")
    axes.set_xlabel("broj koraka $n$")
    axes.set_ylabel("P(sve tačno) $= p^n$")
    axes.set_ylim(0, 1.02)
    axes.legend(loc="lower right", bbox_to_anchor=(1, 0.06))
    return figure


@FIGURES.register("navier_stokes_terms")
def render_navier_stokes_terms(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return EquationTermsDiagram(
        terms=[
            DiagramNode("$\\frac{\\partial u}{\\partial t}$",
                        palette.blue, "promena\nbrzine"),
            DiagramNode("$+$", palette.ink),
            DiagramNode("$(u \\cdot \\nabla) u$", palette.violet,
                        "tok nosi\nsam sebe"),
            DiagramNode("$=$", palette.ink),
            DiagramNode("$-\\nabla p$", palette.aqua, "pritisak"),
            DiagramNode("$+$", palette.ink),
            DiagramNode("$\\nu \\Delta u$", palette.orange,
                        "trenje\n(viskoznost)"),
            DiagramNode("$+$", palette.ink),
            DiagramNode("$f$", palette.red, "spoljna\nsila"),
        ]
    ).render(context)


@FIGURES.register("blowup")
def render_blowup(context: FigureContext) -> plt.Figure:
    palette = context.palette
    time = np.linspace(0, 0.995, 400)
    blowup_time = 1.0
    figure, axes = context.create_figure(DEFAULT_WIDE_SIZE)
    smooth = 1 + 0.6 * np.sin(4 * time) * np.exp(-time)
    axes.plot(time * 1.2, smooth, color=palette.blue,
              label="glatko rešenje: ostaje konačno")
    exploding = 1 / (blowup_time - time) ** 0.5
    axes.plot(time, exploding, color=palette.red,
              label="eksplozija: $|u| \\to \\infty$")
    axes.axvline(blowup_time, color=palette.red, ls="--")
    axes.text(blowup_time + 0.01, 9, "$T^*$", fontsize=20, color=palette.red)
    axes.set_ylim(0, 12)
    axes.set_xlim(0, 1.2)
    axes.set_xlabel("vreme $t$")
    axes.set_ylabel("najveća brzina $\\max|u|$")
    axes.legend(loc="upper left")
    return figure


@FIGURES.register("lean_feedback")
def render_lean_feedback(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return VerificationLoopDiagram(
        producer=DiagramNode("AI agenti\npredlažu dokaz", palette.blue),
        checker=DiagramNode("Lean jezgro\nproverava svaki korak",
                            palette.muted_ink),
        accepted=DiagramNode("✓ dokazano", palette.green),
        rejected=DiagramNode("✗ greška u koraku", palette.red),
        note="poruka o grešci nazad agentu",
    ).render(context)


@FIGURES.register("navier_stokes_timeline")
def render_navier_stokes_timeline(context: FigureContext) -> plt.Figure:
    palette = context.palette
    events = [
        (0, "15. avg", "Buckmaster i Alpöge:\neksplozija forsiranog Ojlera",
         palette.aqua),
        (7, "22. avg", "njihov dokaz\nproveren u Lean-u", palette.violet),
        (17, "1. sep", "OpenAI počinje:\n~10.000 agenata", palette.blue),
        (21, "+88 h", "rezultat, pa\n+17 h Lean", palette.orange),
        (24, "8. sep", "objava: forsirani\nNavier–Stokes", palette.red),
    ]
    return TimelineDiagram(
        events=[
            TimelineEvent(
                label=label, caption=caption, color=color, position=day
            )
            for day, caption, label, color in events
        ],
        spacing=3.0,
    ).render(context)


@FIGURES.register("turing_test")
def render_turing_test(context: FigureContext) -> plt.Figure:
    palette = context.palette
    canvas = context.blank_canvas((10, 5))
    axes = canvas.axes
    canvas.draw_box((-3.5, 0), "sudija", palette.orange, BoxSize(2.2, 1.0))
    canvas.draw_box((3.2, 1.5), "čovek", palette.green, BoxSize(2.2, 1.0))
    canvas.draw_box((3.2, -1.5), "mašina", palette.blue, BoxSize(2.2, 1.0))
    axes.plot([0.6, 0.6], [-2.6, 2.6], color=palette.muted_ink, lw=6)
    axes.text(
        0.6,
        2.9,
        "zid",
        ha="center",
        fontsize=14,
        color=palette.muted_ink,
    )
    canvas.draw_arrow((-2.3, 0.3), (2.0, 1.4), curve=-0.1)
    canvas.draw_arrow((-2.3, -0.3), (2.0, -1.4), curve=0.1)
    axes.text(-0.4, 1.4, "pitanja", fontsize=14, ha="center")
    axes.text(-3.5, -1.3, "Ko je ko?", fontsize=18, ha="center",
              color=palette.ink)
    axes.set_xlim(-5, 4.8)
    axes.set_ylim(-3, 3.3)
    return canvas.figure


@FIGURES.register("formal_system")
def render_formal_system(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return NestedSetsDiagram(
        outer_label="sve istinite tvrdnje",
        inner_label="dokazive\nteoreme",
        gap_label="istinite,\nali\nnedokazive",
        inputs=[
            DiagramNode("aksiome", palette.blue),
            DiagramNode("pravila", palette.violet),
            DiagramNode("simboli", palette.aqua),
        ],
        note="Gedel (1931)",
    ).render(context)


@FIGURES.register("summary_chain")
def render_summary_chain(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return FlowDiagram(
        steps=[
            DiagramNode("model", palette.muted_ink),
            DiagramNode("mašinsko\nučenje", palette.aqua),
            DiagramNode("jezički\nmodel", palette.blue),
            DiagramNode("LLM", palette.violet),
            DiagramNode("agent +\nverifikator", palette.orange),
        ],
        box_size=BoxSize(2.2, 1.2),
        spacing=2.8,
    ).render(context)


def main() -> int:
    return render_registry(
        FIGURES, DEFAULT_OUTPUT_DIRECTORY, default_seed=DEFAULT_SEED
    )


if __name__ == "__main__":
    sys.exit(main())
