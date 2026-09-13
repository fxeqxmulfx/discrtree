# discrtree

`dt` finds a Lean declaration by its **shape** rather than by its name, and
lifts a declaration out of a library into a proof: it prints the declaration
with what it rests on and the `import` line that actually provides it.

```
$ dt find 'Real.exp _ ≤ Real.exp _'
Real.exp_le_exp_of_le  theorem  Mathlib.Analysis.Complex.Exponential
  ∀ {x y : ℝ}, x ≤ y → Real.exp x ≤ Real.exp y
1 result(s)

$ dt show Real.exp_le_exp_of_le --import-only
import Mathlib.Analysis.Complex.Exponential
```

That module is the point. The name suggests
`Mathlib.Analysis.SpecialFunctions.Exp`, which does not contain it.

Name search already exists and works. Shape search is the part the repository
answers badly: a lemma is easy to describe and hard to name. Over 225 508
elaborated Mathlib declarations that query takes 24 ms.

## The one invariant

Every source is either **elaborated** or not, and the difference is not
cosmetic:

| kind | elaborated | importable | what works |
| --- | --- | --- | --- |
| `lake` (Mathlib, a dependency) | yes | yes | shape search, exact dependencies |
| `local` (your own `src/`) | yes | yes | shape search, exact dependencies |
| `git` (a corpus fetched as text) | no | no | name, text, module and `--uses` search |

An elaborated row came out of Lean: its type is the elaborated one, its
conclusion head symbol is read off the `Expr`, and its dependency list is the
set of constants its proof term actually uses. A text row was read by a
scanner: it has no conclusion head symbol, and its dependencies are guessed
from the file's imports and the identifiers it mentions.

Every row carries `elaborated: true|false`, and **every result line from a text
source is marked `[text]`**. A search that silently mixed the two would be
worse than no search. Asking for a shape implies `--elaborated`, because a text
row cannot answer that question and dropping the condition would be a lie.

## Commands

| | |
| --- | --- |
| `dt init` | write a starter `discrtree.toml` |
| `dt dump [source]` | run Lean over a compiled source, writing JSONL |
| `dt fetch [source]` | blobless sparse clone of a text corpus |
| `dt scan [source]` | read a text corpus with the scanner |
| `dt index` | build the SQLite + FTS5 index |
| `dt status` | what is indexed, and whether it is elaborated |
| `dt find <pattern>` | search by shape, name, constants, module or text |
| `dt show <name>...` | the declarations verbatim, and the imports that provide them |
| `dt deps <name>` | what a proof rests on, level by level |
| `dt add <name>` | materialize a declaration and its tree into the project |
| `dt dup <file>` | is this already upstream? |

`dt add` is a dry run by default. The size of the materialization set cannot be
predicted from the name: for a Mathlib target it is empty and the whole answer
is a single `import` line, and for a source that cannot be imported an
arbitrarily deep tree is the normal case.

Dependency closures collapse at the **importable frontier**: an importable
dependency becomes one `import` line and its entire subtree disappears. That is
not a depth cap — it is the reason the answer for a Mathlib lemma is one line
rather than 5000 declarations.

## Output is priced per read

`dt` is read by an agent at least as often as by a person, and an agent pays
for every byte twice: once to receive the answer and again on every later turn
that carries it. The output is shaped accordingly.

* **No alignment padding.** A column of names padded to a fixed width is more
  than half whitespace, and the whitespace says nothing. `dt deps` used to
  spend 61% of its output on it.
* **No blank separators.** Records end where the next one begins.
* **The repeating field is said once.** A dependency level is a set of names
  grouped under its source, not one row per name with `mathlib` restated
  beside each.
* **Ten results, not forty.** The eleventh hit for a query worth asking is
  rarely the wanted one. When the limit hides something the footer says
  `10 shown, more match` rather than letting a truncated answer look complete.
* **The docstring waits for `--long`.** It was a quarter of `dt find` and
  almost never the reason a search succeeded.

Two things it deliberately does *not* do. It does not elide the shared
`Mathlib.` prefix from module names: the module is what gets copied into an
`import` line, and a name that has to be reconstructed is a name that can be
reconstructed wrongly. And there is no `--json`: braces, quotes and repeated
field names cost more than the terse text they would replace.

The measured effect on the real index — 225 508 declarations:

| | before | after |
| --- | ---: | ---: |
| `dt find --name exp` (default limit) | 3952 B | 688 B |
| `dt find --name exp --limit 40` | 3952 B | 2866 B |
| `dt deps Real.exp_le_exp_of_le` | 301 B | 86 B |

What none of this buys is a round trip saved. That is the larger cost, and the
reason `dt find` prints the module on the same line as the name: the module
*is* the import, so a hit is actionable without a second call. For the same
reason `dt show` takes any number of names, prints each import line once, and
reports a name it could not find on stderr rather than failing the batch — a
misremembered name costs one line, not the other four lookups.

## An empty answer says which repair it needs

`no match` is the most expensive line `dt` can print, because on its own it
does not say what to do next. Three situations produce it and they need
opposite repairs:

```
$ dt find --name exp --in Analysis
no match: --in Analysis matches nothing on its own

$ dt find --name exp --uses Finset.sum --in Mathlib.Order
no match: every condition matches on its own; drop one
```

The first is a condition to edit — Mathlib's modules begin `Mathlib.`, so
`Analysis` is not a prefix of any of them. The second is a condition to drop.
Guessing between them costs a search either way; asking each condition on its
own costs one row each, and only when the search has already failed.

Two asks are refused outright rather than answered with an empty result, because
a closed set can name what was meant and a contradiction is not an absence:

```
$ dt find --name exp --source Mathlib
dt: no source `Mathlib`; configured sources are project, mathlib, flt

$ dt find 'Real.exp _ ≤ _' --source flt
dt: source `flt` is text, and a shape can only be matched against elaborated
    rows; search it by --name, --text, --in or --uses instead
```

## Setup

```
cargo install --path .
cd your-lean-project
dt init          # then edit discrtree.toml
dt dump          # minutes: this loads the whole Lean environment
dt index
```

`dt dump` needs `elan` on `PATH` and runs `lake env lean` in the project root,
because only the elaborator can read `.olean` files. Everything after that is
one Rust binary.

## Layout

```
src/domain/          entities and rules; no I/O, no dependencies
src/application/     use cases, written against the ports in ports.rs
src/infrastructure/  the adapters: SQLite, JSONL, lake, git, filesystem
src/interface/       the CLI, the renderer, and the composition root
lean/dump.lean       phase 1: the only part that has to be Lean
```

Dependencies point inward only. Nothing in `domain` knows that SQLite exists.

## Licence

MIT. See [LICENSE](LICENSE).
