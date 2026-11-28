# Showcase

Showcase turns a Lean formalization into a website that reads like a paper: the main results, what
they rest on (axioms, libraries, definitions to read), then the whole development. The Lean
statement and the Lean proof of each result are one click away.

**Example:** [SVGD on a compact domain](https://gaetanserre.fr/CompactSVGD/), the website of
[CompactSVGD](https://github.com/gaetanserre/CompactSVGD).

## Usage

Add a `showcase/` folder to your project, with this `lakefile.toml`:

```toml
name = "site"
packagesDir = "../.lake/packages"

[[require]]
name = "MyProject"
path = "../"

[[require]]
name = "showcase"
git = "https://github.com/gaetanserre/LeanShowcase"
rev = "main"
```

Then build the project and the website:

```bash
lake build
cd showcase && lake exe showcase --module MyProject
```

The website is the folder `showcase/_site/`. It shows every declaration of `MyProject` and of the
files of the project that it imports, with their docstrings. It needs Lean v4.30 or later.

## Writing the text

To write the text yourself, add a file `showcase/showcase.md`, then run `lake exe showcase`.

````markdown
---
title: The mean value theorem
module: MyProject.MeanValue
main: [exists_deriv_eq_slope | Theorem 1]
---

A differentiable function has a tangent parallel to each of its chords.

{{exists_deriv_eq_slope | Theorem 1}}

```sketch exists_deriv_eq_slope
Apply Rolle's theorem to $f$ minus the chord.
```
````

- `{{Name | Label}}` shows the declaration `Name`.
- ` ```informal Name `, ` ```sketch Name ` and ` ```proof Name ` give its statement in words, a short
  proof and a full proof.
- ` ```diagram Name ` draws a map of its proof, and ` ```figure Name ` adds a figure.
- `$...$` and `$$...$$` are TeX, `` `name` `` is a Lean name with a link, `[Key]` is a citation.

The `showcase.md` of [CompactSVGD](https://github.com/gaetanserre/CompactSVGD/blob/main/showcase/showcase.md)
uses all of them.

The main keys of the front matter. Only `module` is required.

| Key | Meaning |
| --- | --- |
| `module` | The file that the text presents. |
| `title`, `subtitle`, `authors`, `abstract` | By default, read from the module docstring. |
| `main` | The main results, shown first. |
| `trusted` | Files of definitions: those that the statements use are shown to be read. |
| `bibliography` | A BibTeX file, for the citations. |
| `docgen` | The API documentation of the project, for the links. |
| `libraries` | Descriptions of the libraries, by package name. |

## Comparator

`lake exe showcase --comparator` first runs
[`lake comparator`](https://github.com/leanprover/comparator), and the website shows its verdict.
On macOS, add `--inadvisably-no-sandbox`.

## Publishing

The [workflow of CompactSVGD](https://github.com/gaetanserre/CompactSVGD/blob/main/.github/workflows/build-project.yml)
builds the website with comparator and publishes it on GitHub Pages.

## License

Apache 2.0. Showcase was developed with [Claude Code](https://claude.com/claude-code).
