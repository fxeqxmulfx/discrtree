# discrtree — plan

Written 2026-09-13. Status: not started.

A CLI for two jobs the repository currently does badly:

1. **Find** a declaration by shape rather than by name, across Mathlib, this
   project and FLT.
2. **Lift** a declaration out of a library and into a proof here — print it,
   with what it rests on and the import it needs.

## Name

`discrtree`, after `Lean.Meta.DiscrTree` — the discrimination tree Lean itself
uses to look up matching lemmas in `exact?`, `apply?` and `simp`. The tool does
the same job from outside the elaborator. Free on crates.io; `sift`, `lq`,
`sieve`, `winnow`, `glean`, `sonar` and most other short English words are
taken. `loogle` is deliberately avoided: that is the existing Lean Hoogle.

Crate `discrtree`, binary `dt`.

## Language: Lean for the dump, Rust for everything else

**Phase 1 must be Lean.** Only the elaborator can read `.olean` and hand back an
elaborated type with notation expanded — without it `∑ i ∈ s, f i` never becomes
`Finset.sum` and shape search has no ground to stand on. That part is ~80 lines
of Lean that write JSONL and stop.

**The rest is one Rust binary.** Not for speed as an abstraction:

* Phase 4 parses 1.17 GB across 60 474 files; with `rayon` over 12 cores that is
  seconds rather than minutes.
* Phase 5 matches expression skeletons over 533 320 declarations. It is the one
  place where the language decides between a 5 ms query and a 5 s query, and a
  5 s search is a search that stops being used.
* One static binary: no venv, no "which python3", no missing module. It is
  called from a shell hundreds of times a day; it should either exist or not.

Honest counterweight: for the index and search alone the language would be
irrelevant — SQLite does the work and Python would be the lighter choice. It is
phases 4 and 5 that tip it.

`scripts/index.py` is **not** rewritten. Different job, 200 lines, works.
Adding Rust is worth one new toolchain, not a migration.

Dependencies: `rusqlite` (feature `bundled`), `rayon`, `serde_json`, `clap`.
FLT's own `nanoda` verifier is Rust too.

## Established facts

Measured on this machine, not assumed.

| | |
|---|---|
| toolchain, ours and FLT's | `leanprover/lean4:v4.33.1`, identical |
| Mathlib revisions | FLT pins the commit immediately before our `v4.33.1` tag; that commit only bumps `lean-toolchain`. Compatible. |
| Mathlib locally | fully built, 8415 `.olean`, 7.2 GB |
| `import Mathlib` | 7.2 s, 7.2 GB resident, **533 320 theorems** |
| this project | 193 theorems |
| FLT sources | `Theorems/` 29 511 files / 275.6 MB · `Definitions/` 1 450 / 12.8 MB · `P2M/Sol/` 29 513 / 882.3 MB |
| machine | 12 cores, 30 GB RAM, 121 GB free |
| rust | cargo 1.98.1 |

Verified by prototype: elaborated types, conclusion head symbol, used constants,
**proof-term dependencies**, module, and exact declaration line ranges all come
out of the environment. Printing `Mathlib/Analysis/Complex/Exponential.lean`
lines 316-318 reproduces `exp_le_exp` verbatim, attribute included.

## Decision: index, never compile

Nothing in the corpus is rebuilt or re-verified here. Upstream verification is
taken on trust — for FLT, its own kernel build, its comparator and its external
`nanoda` check.

For FLT this is also forced: it wants 67 GB of disk and 5 GB of memory per job
against 12 cores and 30 GB of RAM here, which caps us near 6 parallel jobs and
turns the upstream "5-6 hours at 96 threads" into days. Indexing its text costs
~1.2 GB and minutes. FLT's own documentation generator makes the same choice:
*"Nothing here runs Lean; the .lean files are read as text."*

### The consequence, stated once and enforced everywhere

* **Mathlib and this project are compiled.** Types are elaborated, notation
  expanded, proof terms available. Shape search and exact dependencies work.
* **FLT is not.** Types are as written; dependencies can only be approximated
  from `import` lines and identifiers appearing in proof text.

Every row carries `elaborated: true|false` and every result line shows it. A
search that silently mixed the two would be worse than no search.

## Configuration

One `discrtree.toml` at the project root. It declares where the tool writes and
what it indexes; everything else is derived.

```toml
[project]
root      = "."
src       = "src"
namespace = "Transformer"
imports   = "src/Transformer.lean"    # what is already reachable
vendor    = "src/Transformer/Vendor"  # where materialized declarations land

[index]
db  = ".discrtree/index.db"
raw = ".discrtree/jsonl"

[[source]]
name = "project"
kind = "local"
path = "src"

[[source]]
name = "mathlib"
kind = "lake"
path = ".lake/packages/mathlib"
rev  = "v4.33.1"

[[source]]
name        = "flt"
kind        = "git"
url         = "https://github.com/anthropics/fermats-last-theorem"
rev         = "main"
sparse      = ["Theorems", "Definitions", "P2M/Sol"]
exclude     = ["html"]
license     = "Apache-2.0"
attribution = "anthropics/fermats-last-theorem"
```

Two properties drive everything and are **derived from `kind`**, with an
explicit override available:

| `kind` | `elaborated` | `importable` |
|---|---|---|
| `lake`, `local` | true — compiled, dumped from the environment | true |
| `git` | false — indexed as text | false |

`elaborated` decides whether shape search and exact dependencies are available.
`importable` decides whether a dependency collapses into an `import` line or has
to be copied. A `git` source that someone does build can set both to true.

## Lifting a declaration into a proof

The second job. The obvious design — "print the theorem and its transitive
dependencies" — does not survive contact with the numbers:

| declaration | direct deps | transitive closure | of which theorems |
|---|---:|---:|---:|
| `Real.exp_le_exp` | 11 | **5 154** | 2 997 |
| `Real.exp_sum` | 26 | 1 984 | 1 015 |
| `Finset.sum_le_sum` | 29 | 223 | 71 |

A two-line lemma about `exp` rests on 5 154 declarations, because `Real.exp` is
built on the whole Cauchy-sequence and complex-analysis tower. So the raw
closure is never the deliverable. What makes the tree tractable is not a depth
cap but the `importable` flag: **a dependency from an importable source collapses
to one `import` line and its entire subtree disappears with it.** What remains
is the frontier, and the frontier is what gets materialized.

Depth of that frontier is data, not an assumption. It is one file for one source
and a deep tree for another, and the tool must not be tuned to either.

**`dt show <name>`** — the declaration's source verbatim, plus the `import` line
that actually provides it. That import is the real value: `Real.exp_le_exp`
lives in `Mathlib.Analysis.Complex.Exponential`, not the
`Mathlib/Analysis/SpecialFunctions/Exp.lean` one would guess, which does not
contain it at all.

**`dt deps <name> --depth 1`** — the direct dependencies, each tagged by source.
Depth 1-2 is the readable regime and answers "what does this proof rest on".
`--depth all` prints a count first and the list only when asked again.

**`dt add <name>`** — materialize the declaration and its whole tree into the
project:

1. Resolve the closure, cycle-safe. Exact for `elaborated` sources; for text
   sources it is approximated from imports and identifiers, and the result is
   labelled approximate.
2. Partition every node by its source's `importable`. Importable nodes become
   `import` lines and take their subtrees with them.
3. What is left is the materialization set. **This is where an arbitrarily deep
   tree shows up, and it is the normal case for a non-importable source, not an
   edge case.**
4. **Dry run by default.** Report, per source: declarations, files, total lines,
   and the depth of the tree. Nothing is written without `--write`. The dry run
   exists precisely because depth cannot be predicted from the name.
5. On `--write`: emit in topological order under `[project] vendor`, one file
   per origin module, each with a provenance header naming source, upstream
   path, revision and license; add the required imports; register the new
   modules in `[project] imports` so they are actually built.

For a Mathlib target the materialization set is empty and the whole answer is
one import line — which is the correct outcome, not a degenerate one. Copying is
right only for a source that cannot be imported.

## Interactions with existing project rules

`dt add` writes code into `src/`, so it collides with three conventions in
`CLAUDE.md`. Resolve them before the first `--write`, not after:

* **Namespaces.** Vendored code keeps its origin namespace and must not be
  bent to `Transformer.` + directory path. The namespace check needs an
  exemption for `[project] vendor`.
* **`INDEX.md` counts.** Vendored declarations would otherwise inflate the
  theorem count and blur the debt figures. `scripts/index.py` should report them
  in a separate section, never mixed into the project's own totals.
* **Licensing.** Materialized Mathlib or FLT code is Apache-2.0. The provenance
  header is a requirement, not decoration, and a repository-level `NOTICE` is
  needed once anything is vendored.

## Phases

**0. Config — an hour.** `discrtree.toml` and its loader. Everything downstream
reads sources and paths from it; nothing hardcodes Mathlib or FLT.

**1. Environment dump — half a day.** `tools/discrtree/dump.lean`, run through
`lake env lean` over each `elaborated` source. Emits JSONL: name, module, kind,
pretty-printed type, conclusion head symbol, used constants, direct
dependencies, docstring, `sorry` flag, and declaration line range. Prototypes
confirm every field.

**2. `dt show` / `dt deps` — half a day.** Needs only name → (module, range,
deps); no index. Ships the lifting problem first because that is the live pain.

**2b. `dt add` — one day.** Frontier computation, dry run, topological
materialization with provenance headers. Held back from 2 because it is the only
command that writes into `src/`, and the three rule collisions above have to be
settled first.

**3. Index and search — one day.** SQLite + FTS5 over type and docstring, plain
columns for conclusion head and constants so conditions combine with `AND`.
~200 MB, millisecond queries. Database gitignored, generator committed.

```
dt find --concl LE.le --uses Real.exp,Finset.sum   # shape — the main mode
dt find 'Real.exp _ ≤ _'                           # by pattern
dt find --name exp_le --in Mathlib.Analysis        # by name, module-filtered
dt dup src/Transformer/ALM/Basic.lean              # already in Mathlib?
```

**4. FLT text corpus — one day.** Sparse blobless clone of `Theorems/`,
`Definitions/`, `P2M/Sol/`; never `html/` (390 MB), never `.lake`. Extraction is
a parse against a known shape, not a heuristic: each `Theorems/Thm_<name>.lean`
holds exactly one theorem, statement inline, proof delegated to
`P2M/Sol/S_<name>.lean`:

```lean
theorem Algebra.norm_of_subsingleton {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [Subsingleton A] (a : A) : Algebra.norm R a = 1 := by
  p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_of_subsingleton.solution
```

Filename gives the name; the statement is what lies between `theorem <name>` and
`:= by p2m_exact_reverting`. Rows carry `elaborated: false`.

**5. Real shape matching — one day, deferred.** Store a signature key per
declaration: conclusion head symbol plus the sorted head symbols of its
arguments to depth 2, so `_ ≤ Real.exp _` and `Real.exp _ ≥ _` land in one
bucket and variable names stop interfering. Elaborated corpora only. Do this
after 1-4 have been in use for a week, when it is clear which queries are
missing.

## What the FLT corpus is worth here

Stated plainly so priorities are not set on a false premise.

**Mathematically it does not overlap with this project.** FLT is elliptic
curves, Galois representations and modular forms; this repository is analysis on
spheres, gradient flows, softmax dynamics, ODEs and measures. What the two share
is Mathlib, which is already here and already built. Do not expect a lemma from
FLT to close a goal in `Transformer.*`.

What it does provide:

* **29 511 Mathlib-style statements and 29 513 tactic proofs at our exact
  toolchain** — a reference for how a given kind of statement is phrased and
  proved in Lean 4.33, regardless of subject.
* **A worked layout for a large Lean project.** Its `Definitions/` /
  `Theorems/` / `P2M/Sol/` split is exactly the by-declaration-kind grouping
  this repository's conventions argue against; it works there because
  `Theorems/` is a showcase surface, not an import layer. Worth reading before
  treating that question as settled.
* **A verification harness aimed at this repository's actual defect.** Its
  comparator checks a proved statement against an independently written
  challenge statement; `nanoda` re-checks every declaration in an external
  kernel. Per `INDEX.md` this repository carries 82 vacuous statements and 20
  placeholder definitions — and a theorem proved as `True` can never match an
  independently written statement of itself. Adapting the comparator is a
  separate task from this plan, and by value it ranks above phase 5.

## Layout

```
discrtree.toml                 # sources, project root, vendor dir
tools/discrtree/Cargo.toml     # package discrtree, binary dt
tools/discrtree/dump.lean      # phase 1, run via lake env lean
tools/discrtree/src/main.rs    # phases 0, 2-5
.discrtree/                    # gitignored: *.jsonl, index.db
```

`dump.lean` sits beside the binary rather than in `scripts/`: the two are halves
of one tool, split across languages only by the constraint above.

## Open questions

* Re-dump automatically on a Mathlib bump, or leave it manual.
* Whether `dt add` should vendor one file per origin module or one per
  declaration. Per module keeps the source readable and diffable against
  upstream; per declaration keeps the tree minimal. Decide on the first real
  deep tree, not before.
* How `dt add` re-runs when upstream moves: re-materialize and diff, or pin the
  revision in the provenance header and leave it frozen.
