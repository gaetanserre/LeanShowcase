# Showcase

A website for the readers of a Lean formalization, in particular those who do not know Lean.
It is not an API documentation (docgen does that). It reads like a paper, and it first shows what
the results rest on, in four screens.

1. **Libraries.** Lean, Mathlib, and the other libraries of `lake-manifest.json` (Tau Ceti, ...),
   marked as outside Mathlib, with the number of their modules that the formalization imports. The
   dependencies of Mathlib (Batteries, Aesop, ...) are counted with Mathlib and not listed.
2. **Axioms.** The axioms used by the displayed results, computed by Lean, with an explanation, the
   Lean statement and links.
3. **Definitions.** The definitions of the project that the displayed statements depend on,
   through their types and the bodies of definitions, and all the definitions of the files listed
   as `trusted`. No checker can tell whether they mean what they should, so they are shown in full.
4. **Results.** The text of the paper, with a card for each result: the informal statement (the
   docstring), the informal proof (the comments of the Lean proof), the Lean statement as Lean
   elaborates it (every name links to its definition), and the Lean source.

The reader accepts the first three screens before the results. A badge links to an explanation of
`lake comparator` and of the checkers it runs.

The output is a single `index.html`, with no server and no build step for the reader.

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

The site is written to `showcase/_site/index.html`.

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
title: Mean-field SVGD on a compact domain
module: CompactSVGD.Paper
trusted: [CompactSVGD.Definitions]
docgen: https://gaetanserre.github.io/CompactSVGD/docs/
---

Stein's identity is the starting point.

{{ProbabilityTheory.stein_identity | Lemma A.3}}
```

A line `{{Name}}` or `{{Name | Label}}` displays the declaration `Name` with the label `Label`
(`Theorem 3.1`, `Definition A.5`, ...). The name is resolved in the namespaces of the file, so
`{{weak_convergence}}` works inside `namespace SVGD`. Without any such line, the website shows every
declaration of `module`, in the order of the file, with its module docstrings: the whole file.

In the text and in the docstrings, a code span that mentions a known constant is shown as Lean code
with links (`` `SVGD.direction` ``), and the others as mathematics (`` `𝔎(μ ∣ π) = ‖φ*_μ‖²` ``, where
`_x`, `_{...}`, `^x` and `^{...}` are sub- and superscripts). `[Key]` cites an entry of the
bibliography.

A block ```` ```informal Name ```` gives the mathematical version of the declaration `Name` (or of
a notation, written as on the definitions screen, e.g. `𝓗[d, H₀]`). It replaces the docstring on
the definitions screen, and it does not appear in the text of the paper:

````markdown
```informal SVGD.pairing
Let $H_0$ be a real inner product space and $h \in H_0^d$. The pairing of $h$ is the map
$$P_h : H_0 \to \mathbb{R}^d, \qquad u \mapsto (\langle h_i, u \rangle)_i.$$
```
````

A title after a bar, ```` ```informal SVGD.pairing | The pairing $P_h$ ````, replaces the title of
the docstring (its leading `**Title**`) on the card, in the table of contents and on the definitions
screen. On the definitions screen, the Lean name is shown next to it.

A block ```` ```proof Name ```` gives the mathematical proof of the result `Name`. It is folded
under its statement, and the reader unfolds it.

A link `[Lemma 2](#Name)` goes to the card of `Name` in the results, or to its item on the
definitions screen. It lets the mathematical texts refer to a result without naming a Lean
declaration.

Mathematics in TeX is written `$...$` in the text and `$$...$$` for a displayed formula, as in
docgen, and rendered with MathJax. An inline formula is never separated from the punctuation that
follows it by a line break.

### Keys

Only `module` is required.

| Key                              | Default                                             | Meaning                                                                                         |
| -------------------------------- | --------------------------------------------------- | ----------------------------------------------------------------------------------------------- |
| `module`                         |                                                     | The module whose results are displayed.                                                         |
| `trusted`                        | `[]`                                                | Modules whose definitions are all listed on the definitions screen.                             |
| `title`, `abstract`              | first heading and paragraph of the module docstring |                                                                                                 |
| `subtitle`, `paper`, `paper_url` |                                                     | Shown on the first screen.                                                                      |
| `authors`                        | the `Authors:` line of the module header            | A list.                                                                                         |
| `docgen`                         |                                                     | The docgen of the project, for the links to its declarations.                                   |
| `docgen_external`                | Mathlib's docgen                                    | The docgen of the dependencies.                                                                 |
| `docgen_packages`                |                                                     | A map from package names to docgen URLs.                                                        |
| `links`                          |                                                     | A map from declaration names to a page about them (Wikipedia, ...).                             |
| `libraries`                      | built in for common packages                        | A map from package names to descriptions.                                                       |
| `axioms`                         | built in for Lean's axioms                          | A map from axiom names to descriptions.                                                         |
| `bibliography`                   |                                                     | A BibTeX file.                                                                                  |
| `comparator`                     | `comparator.json` of the project                    | The configuration of `lake comparator`: the checked theorems get a badge.                       |
| `comparator_report`              | `comparator-report.json`                            | The output of `lake comparator --json`, written by `--comparator`. The badge shows its verdict. |
| `checkers`                       |                                                     | The checkers to show on the badge when there is no report.                                      |
| `repository`, `rev`              | `git remote get-url origin`, `git rev-parse HEAD`   | For the links to the source.                                                                    |
| `output`                         | `_site`                                             | The output folder.                                                                              |

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
* `lake-manifest.json` and the location of every imported `.olean`, for the libraries.

It then fills the template of `assets/` with this data. The site uses no JavaScript library, except
MathJax for the mathematics.

## AI Disclaimer

Showcase was developed with [Claude Code](https://claude.com/claude-code), the AI coding assistant of
Anthropic.

## License

Apache 2.0. See [LICENSE](LICENSE).
