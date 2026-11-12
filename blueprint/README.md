# ACVF-QE Lean blueprint

The blueprint maps the completed ACF, ordinary ACVF, and RV-language QE proofs
into 22 selected theorem/definition nodes. Each node links to the
exact Lean declaration and records its mathematical dependencies. These are
selected proof dependencies, not a complete expression-level dependency graph.

[Live blueprint](https://daviddhilbert.github.io/ACVF-QE/)
· [Theorem dependency graph](https://daviddhilbert.github.io/ACVF-QE/dependency-graph.svg)

Trivial and nontrivial valuation cases are kept separate. Named RV inversion,
the canonical trivial RV theory, arbitrary parameter indices, and the absence
of a CH assumption are explained in the statements. The blueprint distinguishes
intermediate conditional interfaces from their discharged inputs in the public
QE theorem. C-minimality is outside this package's claims.

## Source identity and verification

The linked proof revision is `939346b0a99899e22a873479364e3cc5d142731c`, with
[passing QE verification](https://github.com/daviddhilbert/ACVF-QE/actions/runs/42689540057).
The Lean sources, toolchain, dependency pins and proof verifier are unchanged.
`proof-source-manifest.json` fingerprints them. Blueprint validation checks
those fingerprints, every declaration anchor, the graph's acyclicity and the
rendered source links. This documentation check is distinct from a fresh Lean
compiler/type/axiom audit.

## Build

With Python, Graphviz and its development headers installed, run from the
repository root:

```sh
python -m pip install -r blueprint/requirements.txt
python scripts/check_blueprint.py
leanblueprint web
python scripts/check_blueprint.py --rendered
```

Open `blueprint/web/index.html` and select **Open the theorem dependency graph**.
The SVG works from a local file; each node opens its statement. The web source
is `src/content.tex`, and `nodes.json` records the node/declaration mapping.
`src/source-links.tsv` records checked source locations. Green nodes indicate
existing checked Lean implementations; they do not add new mathematical claims.

An optional print source is provided in `src/print.tex`; `leanblueprint pdf`
requires a LaTeX distribution and `latexmk`. The web deployment does not require
LaTeX or downloading Lean build dependencies.

## Reuse and attribution

The blueprint scaffolding and static clickable dependency-graph helper are
adapted from the MIT-licensed
[Special transformations blueprint](https://github.com/daviddhilbert/special-transformations/tree/f76d100e07c0a791259244fc7fdf06f4dfaaf8ae/blueprint).
The renderer is Patrick Massot's `leanblueprint` 0.0.20. Existing proof-source
credits, including Elliot Glazer's Apache-2.0 saturated-extension adaptation,
remain in the repository and are not replaced by this documentation.
