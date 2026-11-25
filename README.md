# Showcase

A website for the readers of a Lean formalization, in particular those who do not know Lean.
It is not an API documentation (docgen does that). It reads like a paper, and it first shows what
the results rest on, in four screens.

1. **Libraries.** Lean, Mathlib, and the other libraries of `lake-manifest.json` (Tau Ceti, ...),
   marked as outside Mathlib, with the number of their modules that the formalization imports. The
   dependencies of Mathlib (Batteries, Aesop, ...) are counted with Mathlib and not listed. With a
   `comparator.json`, the libraries to trust are those that its `challenge_module` imports,
   directly or transitively. Comparator checks the statements against the challenge and replays
   the proofs, so a library that only the proofs import is listed apart, as checked by comparator.
   The module counts follow the same split.
2. **Axioms.** The axioms used by the displayed results, computed by Lean, with an explanation, the
   Lean statement and links.
3. **Definitions.** The definitions of the project that the displayed statements depend on,
   through their types and the bodies of definitions, and all the definitions of the files listed
   as `trusted`. No checker can tell whether they mean what they should, so they are shown in full.
4. **Results.** The text of the paper, with a card for each result: the informal statement (the
   docstring), its proof as a map of its arguments or as a short sentence (or else the comments of
   the Lean proof), the Lean statement as Lean elaborates it (every name links to its definition),
   and the Lean source.

The reader accepts the first three screens before the results. A badge links to an explanation of
`lake comparator` and of the checkers it runs.

The output is a static folder. It holds `index.html`, with the data and the code of the page, and the
images and the favicon next to it. The reader needs no server and no build step.

For a complete example, see [CompactSVGD](https://github.com/gaetanserre/CompactSVGD). Its website
is generated from `showcase/showcase.md`, with proof maps, short proofs and figures.

## Setup in a project

Three small files in a `showcase/` folder of the project. The folder is a separate Lake workspace
(like the `docbuild/` folder of docgen), so the project itself does not depend on `showcase`, and
`lake comparator` does not have to trust it.

`showcase/lakefile.toml`:

```toml
name = "site"
reservoir = false
packagesDir = "../.lake/packages"

[[require]]
name = "MyProject"
path = "../"

[[require]]
name = "showcase"
git = "https://github.com/gaetanserre/LeanShowcase"
rev = "main"
```

`showcase/.gitignore`:

```
/.lake
/_site
```

`showcase/showcase.md`, described below. Then, from the root of the project:

```bash
lake build
```

```bash
cd showcase && lake exe showcase
```

The site is written to `showcase/_site/`.

To run `lake comparator` first and show its verdict on the website:

```bash
cd showcase && lake exe showcase --comparator
```

This runs `lake comparator --json --paranoid` in the project, writes its report to
`showcase/comparator-report.json`, then generates the website. On macOS, where comparator's sandbox
(`bubblewrap`) does not exist, add `--inadvisably-no-sandbox`: the website then says that the run was
not sandboxed. `--no-paranoid` skips the external checkers. Without `--comparator`, the last report
is used if there is one.

## `showcase.md`

A front matter between `---` lines, then the text of the paper in Markdown.

```markdown
---
title: The mean value theorem
module: MyProject.MeanValue
trusted: [MyProject.Defs]
docgen: https://example.org/MyProject/docs/
---

A differentiable function has a tangent parallel to each of its chords.

{{exists_deriv_eq_slope | Theorem 1}}
```

A line `{{Name}}` or `{{Name | Label}}` displays the declaration `Name` with the label `Label`
(`Theorem 3.1`, `Definition 2`, ...). It can also be a declaration of a dependency, such as
Mathlib, shown with its source and a link to its docgen. The name is resolved in the namespaces that
the file enters or opens, so `{{Icc_subset_Icc}}` works after `open Set`. Without any such line, the
website shows every declaration of `module`, in the order of the file, with its module docstrings:
the whole file.

In the text and in the docstrings, a code span that mentions a known constant is shown as Lean code
with links (`` `deriv` ``), and the others as mathematics (`` `‖x‖^2 = ∑_i x_i^2` ``, where
`_x`, `_{...}`, `^x` and `^{...}` are sub- and superscripts). `[Key]` cites an entry of the
bibliography.

A block ```` ```informal Name ```` gives the mathematical version of the declaration `Name` (or of
a notation, written as on the definitions screen, e.g. `𝔼[X]`). It replaces the docstring on
the definitions screen, and it does not appear in the text of the paper:

````markdown
```informal deriv
Let $f : \mathbb{R} \to \mathbb{R}$ and $x \in \mathbb{R}$. The derivative of $f$ at $x$ is
$$f'(x) = \lim_{h \to 0} \frac{f(x + h) - f(x)}{h}$$
if this limit exists, and $f'(x) = 0$ otherwise.
```
````

A title after a bar, ```` ```informal deriv | The derivative ````, replaces the title of
the docstring (its leading `**Title**`) on the card, in the table of contents and on the definitions
screen. On the definitions screen, the Lean name is shown next to it.

A block ```` ```proof Name ```` gives the mathematical proof of the result `Name`. It is folded
under its statement, and the reader unfolds it.

A block ```` ```sketch Name ```` gives a short proof of `Name`, in one or two sentences. It is shown
under the statement, after *Proof idea.*

A block ```` ```diagram Name ```` draws the proof of `Name` as a map: boxes for the facts it uses and
the steps it takes, and an arrow from each fact to the step that uses it. Each box is a line
`id: head <- dep, dep`, followed by its text on indented lines, and by an explanation on indented
lines that start with `>`. The head says what the box is.

* `` `Name` ``, a code span alone: a result of the page, labelled as on the page. The box links to
  its card, and its explanation is its statement.
* `step`: a step of the proof.
* `goal`: the conclusion, labelled like the card.
* any other text: a classical theorem, with its name, then the Lean name of its statement as a code
  span, then a citation `[Key]`. The box names the library that proves it (Mathlib, Tau Ceti, the
  project, ...), and its explanation links to the Lean statement.

````markdown
```diagram exists_deriv_eq_slope
h: step
  $h(x) = (b - a) f(x) - (f(b) - f(a)) x$
  > $h$ is continuous on $[a, b]$, differentiable on $(a, b)$, and $h(a) = h(b) = b f(a) - a f(b)$.
rolle: Rolle's theorem `exists_hasDerivAt_eq_zero` <- h
  $h'(c) = 0$ for some $c \in (a, b)$
goal <- rolle
  $f'(c) = \frac{f(b) - f(a)}{b - a}$
```
````

The map is laid out with [dagre](https://github.com/dagrejs/dagre), top to bottom. A map wider than
the card is scaled down. The reader selects a box to see its explanation under the map, and hovering
a box shows the facts it rests on.

A block ```` ```figure Name ```` adds a figure to the card of `Name`, under its statement. A block
```` ```figure ```` without a name stays in the text, where it is written. Each line `path` or
`path | caption` is an image, and the other lines are the caption of the figure. Several images are
set side by side, labelled a), b), ... The figures are numbered in the order of the page, and a click
enlarges an image. An image alone is at most 1.6 times its own size. Thus, a text set at 9pt in the
figure is about as large as the text of the page. An image can also be written `![alt](path)` in
the text.

````markdown
```figure exists_deriv_eq_slope
figures/chord.svg | $f(x) = x^3$
figures/tangent.svg | $f(x) = \sin x$
The chord between $a$ and $b$, and the tangent at $c$, parallel to it. **a)** ... **b)** ...
```
````

The paths of the images are relative to `showcase.md`, inside its folder. Each image is copied to
the output folder at the same path, and a missing image stops the generation before anything else.
An image given by a URL is left to the browser. The formats are SVG, PNG, JPEG, GIF, WebP and AVIF.
The page reads the size of an SVG or PNG image, to keep its place while it loads.

A link `[Lemma 2](#Name)` goes to the card of `Name` in the results, or to its item on the
definitions screen. It lets the mathematical texts refer to a result without naming a Lean
declaration.

Mathematics in TeX is written `$...$` in the text and `$$...$$` for a displayed formula, as in
docgen, and rendered with MathJax. An inline formula is never separated from the punctuation that
follows it by a line break.

### Keys

Only `module` is required.

| Key                              | Default                                             | Meaning                                                                                                                              |
| -------------------------------- | --------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------ |
| `module`                         |                                                     | The module whose results are displayed.                                                                                              |
| `trusted`                        | `[]`                                                | Modules whose definitions are all listed on the definitions screen.                                                                  |
| `title`, `abstract`              | first heading and paragraph of the module docstring |                                                                                                                                      |
| `subtitle`, `paper`, `paper_url` |                                                     | Shown on the first screen.                                                                                                           |
| `authors`                        | the `Authors:` line of the module header            | A list.                                                                                                                              |
| `docgen`                         |                                                     | The docgen of the project, for the links to its declarations.                                                                        |
| `docgen_external`                | Mathlib's docgen                                    | The docgen of the dependencies.                                                                                                      |
| `docgen_packages`                |                                                     | A map from package names to docgen URLs.                                                                                             |
| `links`                          |                                                     | A map from declaration names to a page about them (Wikipedia, ...).                                                                  |
| `libraries`                      | built in for common packages                        | A map from package names to descriptions.                                                                                            |
| `axioms`                         | built in for Lean's axioms                          | A map from axiom names to descriptions.                                                                                              |
| `bibliography`                   |                                                     | A BibTeX file.                                                                                                                       |
| `comparator`                     | `comparator.json` of the project                    | The configuration of `lake comparator`. The checked theorems get a badge. Only the libraries that its challenge imports are trusted. |
| `comparator_report`              | `comparator-report.json`                            | The output of `lake comparator --json`, written by `--comparator`. The badge shows its verdict.                                      |
| `checkers`                       |                                                     | The checkers to show on the badge when there is no report.                                                                           |
| `repository`, `rev`              | `git remote get-url origin`, `git rev-parse HEAD`   | For the links to the source.                                                                                                         |
| `output`                         | `_site`                                             | The output folder.                                                                                                                   |
| `favicon`                        | the icon of Showcase, `⊢` on a blue square          | An image, relative to `showcase.md`.                                                                                                 |

Paths are relative to `showcase.md`. Values are strings, inline lists `[a, b]`, lists of `- item`
lines, maps of indented `key: value` lines, or text blocks introduced by `>` (lines joined) or `|`
(lines kept).

### Writing the informal proofs

The informal proof of a theorem is the list of the comments (`--` and `/- -/`) of its Lean proof,
in order. Nested comments (more indented) are shown nested. When a proof uses other lemmas of the
file, they are listed with their own statement and informal proof; the private ones are followed
recursively.

## Publishing with GitHub Pages

```yaml
- name: Install bubblewrap, for the sandbox of comparator
  run: sudo apt-get install -y bubblewrap
- name: Build the website
  run: |
    lake build
    cd showcase && lake exe showcase --comparator
- uses: peaceiris/actions-gh-pages@v4
  with:
    github_token: ${{ secrets.GITHUB_TOKEN }}
    publish_dir: showcase/_site
```

On Linux, comparator runs in its sandbox, and the website says so.

## How it works

`lake exe showcase` imports the compiled formalization (it must be built first) and reads:

* the declaration ranges, to cut the source of each declaration into statement and proof;
* the docstrings and module docstrings;
* the pretty-printed signatures, with the notations of the opened namespaces, and the constant of
  every token, for the links;
* `collectAxioms`, for the axioms;
* the constants used by the types and the bodies of definitions, for the definitions to trust;
* `lake-manifest.json` and the location of every imported `.olean`, for the libraries;
* the imports of the challenge module of comparator, read from its source and followed through
  every kind of import, for the libraries to trust.

It then fills the template of `assets/` with this data, and copies the images and the favicon next
to the page. The page has a single, light theme. The site uses two JavaScript libraries,
loaded from a CDN: MathJax for the mathematics, and dagre for the layout of the proof maps.

## AI Disclaimer

Showcase was developed with [Claude Code](https://claude.com/claude-code), the AI coding assistant of
Anthropic.

## License

Apache 2.0. See [LICENSE](LICENSE).
