# discrtree

`dt` finds a Lean declaration by its **shape** rather than by its name, and
lifts a declaration out of a library into a proof: it prints the declaration
with what it rests on and the `import` line that actually provides it.

```
$ dt find 'Real.exp _ ≤ Real.exp _'
Real.exp_le_exp_of_le
  theorem  Mathlib.Analysis.Complex.Exponential
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
| `dt show <name>` | the declaration verbatim, and the import that provides it |
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
