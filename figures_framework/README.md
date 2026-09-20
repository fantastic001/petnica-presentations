# figures_framework

A small, reusable framework for the figures used by the presentations in
this repository. Every presentation keeps a `figures.py` that only
*declares* what a figure contains; the framework owns style, layout,
output and the command line.

## Running a presentation's figures

```sh
.venv/bin/python naucni-metod/figures.py
```

Configuration comes from the environment, so nothing has to be edited in
code:

| Variable | Meaning | Default |
|---|---|---|
| `FIGURES_OUTPUT_DIR` | where files are written | `<presentation>/img` |
| `FIGURES_FORMAT` | `svg`, `png` or `pdf` | `svg` |
| `FIGURES_DPI` | resolution of raster parts and of `png` output | `300` |
| `FIGURES_SEED` | seed for every random figure | per presentation |
| `FIGURES_ONLY` | comma separated figure names | all |
| `FIGURES_STYLE` | `light` or `dark` | `light` |
| `FIGURES_MODE` | `rebuild` or `resume` | `rebuild` |

`resume` is the checkpoint mode: figures whose output file already exists
are skipped, so an interrupted run continues where it stopped.

## Declaring a figure

```python
FIGURES = FigureRegistry("naucni-metod")

@FIGURES.register("scientific_cycle")
def render_scientific_cycle(context: FigureContext) -> plt.Figure:
    palette = context.palette
    return CycleDiagram(
        steps=[
            DiagramNode("Posmatranje", palette.blue),
            DiagramNode("Hipoteza", palette.orange),
            DiagramNode("Eksperiment", palette.green),
        ],
        center_note="nove\npredikcije",
    ).render(context)


def main() -> int:
    return render_registry(FIGURES, DEFAULT_OUTPUT_DIRECTORY)
```

A renderer receives a `FigureContext` (palette, seeded random generator)
and returns a figure. Saving, seeding, style, selection and error
handling happen outside of it.

## Diagram catalogue

No call site computes coordinates. A diagram is described by its content;
the builder derives positions, the bounding box and the figure size.

| Builder | Use it for |
|---|---|
| `FlowDiagram` | a pipeline of steps, optional captions and feedback arrow |
| `MergeFlowDiagram` | several inputs joining into one process and output |
| `StackedDiagrams` | two or more labelled rows of the above |
| `CycleDiagram` | a closed loop, laid out as a ring or as two columns |
| `HubDiagram` | one system with labelled inputs, outputs and influences |
| `FeedbackLoopDiagram` | controller, action, observation, goal |
| `VerificationLoopDiagram` | producer, checker, accept and reject branches |
| `LayeredStackDiagram` | a vertical stack, optionally with a repeated group |
| `LayeredNetworkDiagram` | layers of nodes with all-to-all edges |
| `TimelineDiagram` | dated events above and below one axis |
| `SpectrumDiagram` | a gradient scale with marks and two end captions |
| `FunnelDiagram` | a chain whose boxes shrink at every step |
| `SplitDiagram` | a sample randomly split into groups |
| `MappingDiagram` | a set of outcomes mapped onto a number line |
| `SequenceDiagram` | a row of items with one highlighted span |
| `EquationTermsDiagram` | an equation whose terms carry captions |
| `NestedSetsDiagram` | one set inside another, with labelled inputs |

## Layout rule

A builder returns an extent $E = [x_0, x_1] \times [y_0, y_1]$ in data
units. After padding $p$ the figure size in inches is

$$
w = \frac{(x_1 - x_0) + 2p}{s_x}, \qquad
h = \frac{(y_1 - y_0) + 2p}{s_y},
$$

clamped to the range in `FigureScale`, where $s_x$ and $s_y$ are the
horizontal and vertical units per inch. Because the data range and the
figure size grow together, text keeps the same physical size no matter
how many elements a diagram holds.

## Modules

| Module | Responsibility |
|---|---|
| `palette.py` | colour sets (`light`, `dark`), validated for colour vision |
| `style.py` | matplotlib defaults derived from a palette |
| `layout.py` | extents, even spacing, sides, figure scale |
| `schematics.py` | low level canvas: boxes, arrows, chains, timelines |
| `diagrams/` | the builders in the table above |
| `mathtools.py` | shared distributions and polynomial fitting |
| `registry.py` | figure registration and selection |
| `runner.py` | seeding, rendering, checkpointing, error reporting |
| `output.py` | writing files in a chosen format |
| `settings.py` | environment configuration |
| `cli.py` | `render_registry`, the single entry point |

## Extending it

Add a palette to `PALETTES`, a style to `STYLE_PROFILES`, or a new
builder under `diagrams/` that implements `render(context) -> Figure`.
Presentations can also merge registries with `FigureRegistry.include`,
which is how a shared set of figures could be reused across decks.
