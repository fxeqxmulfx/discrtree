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

Shape search is not missing from Lean. Mathlib ships `#find`, the elaborator
has `exact?` and `apply?`, and `#loogle` asks the same question over the
network — all of them built on the discrimination tree this tool is named
after. What they need is a Lean session. The query above, asked both ways over
the same Mathlib:

| | answer | time | peak memory |
| --- | --- | ---: | ---: |
| `#find Real.exp _ ≤ Real.exp _` after `import Mathlib` | found it | 377.54 s | 7.45 GB |
| `dt find 'Real.exp _ ≤ Real.exp _'` | found it | 0.03 s | 8 MB |

And `import Mathlib` is the cheat. `#find` searches the environment of the file
it runs in, so without `import Mathlib.Analysis.Complex.Exponential` the lemma
is not merely unfound — the pattern will not elaborate at all:

```
$ lake env lean A.lean          # A.lean imports only Mathlib.Tactic.Find
A.lean:2:6: error: Unknown identifier `Real.exp`
```

That is the whole difficulty. You are searching in order to find out what to
import, and the search will not run until you have imported it. `dt` reads an
index rather than an environment, so it answers before the import exists and
its answer *is* the import line. It also reaches corpora that were never
compiled — the 58 674 declarations of FLT below, which no `#find` can see.

A lemma is easy to describe and hard to name. That much was always true; what
was missing was somewhere cheap to ask.

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
| `dt skill` | print the agent skill; `--install` writes it into `.claude/skills/` |
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

The measured effect, on an index of 225 508 declarations:

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

`dt skill` prints the whole interface in 32 lines — the rules that are not
guessable, and nothing else. It is meant to be read once by an agent instead of
eleven `--help` screens, and `dt skill --install` drops it into
`.claude/skills/discrtree/SKILL.md` so it is loaded only when it is needed. The
text is compiled into the binary from that same file, so the printed copy and
the shipped one cannot drift apart.

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

## A declaration Lean wrote has no source of its own

57 443 of Mathlib's 325 936 rows have a source range sitting inside another
declaration's, and in a random sample of 250 rows, 29 declared nothing at their
own lines. They were generated rather than typed: `to_additive`
turns `Finset.prod_image` into `Finset.sum_image`, `@[simps]` turns a definition
into its simp lemmas, `alias` renames, a structure yields its fields and its
constructor. Lean gives each of them a range all the same, and that range points
at the syntax that produced it: an attribute block, a field line, the first line
of a `structure`. Printed as if it were the declaration, it reads like an answer
and stops exactly where the useful part begins.

```
$ dt show Finset.sum_image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

Finset.sum_image
  theorem  Mathlib.Algebra.BigOperators.Group.Finset.Basic:92-94
  generated inside Finset.prod_image:90-97; `dt show Finset.prod_image` has the source

∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst : AddCommMonoid M] {f : ι → M}
  [inst_1 : DecidableEq ι] {s : Finset κ} {g : κ → ι},
  Set.InjOn g ↑s → ∑ x ∈ Finset.image g s, f x = ∑ x ∈ s, f (g x)
```

Two questions settle it, and neither needs Lean: do those lines declare this
name, and if not, which declaration contains them? The walk continues outward
while the container is generated too — `MonoidHom.mk` sits inside the projection
`MonoidHom.toMulHom`, which sits inside `structure MonoidHom`, and only the last
of the three was written by anyone. `dt add` resolves the same way and copies
the generator once for both halves of a pair: an attribute block vendored with
no declaration under it is a file that does not compile.

## Staying current

An index is a snapshot, and the dangerous failure is not a stale answer but a
confident one: an `import` line for a module that was renamed two Mathlib bumps
ago looks exactly like a correct answer. So every source records what it was
built from, and `dt status` reports both that and where the source is now.

```
source         kind    elaborated   importable   declarations  indexed  revision
project        local   true         true                  470  2h ago   -
mathlib        lake    true         true               225508  2h ago   0000000 stale
flt            git     false        false               58674  2h ago   aa2d8b3

behind the checkout: mathlib — re-run `dt fetch`, `dt dump` and `dt index`
```

A compiled source's revision comes from `lake-manifest.json`, which is what the
next `lake build` will honour, and a text source's from the checkout's `HEAD`.
A source with no revision to read is reported as `-` and never as stale: a
warning that is always on is a warning nobody reads.

`dt index` leaves alone any source whose input has not changed since it was
indexed. The input is the dump for a compiled source and the checkout for a
text one, fingerprinted by size and mtime in the first case and by revision in
the second — so a Mathlib bump that has not been dumped again changes nothing,
which is correct, because the index is built from the dump.

| | |
| --- | ---: |
| `dt index` with nothing changed | 0.03 s |
| `dt index` after one source moved | 125 s |
| `dt index --rebuild` | 93 s |

Re-indexing one large source in place costs *more* than starting over, because
the rows have to be deleted before they are written and the text index is
rebuilt either way. That is worth knowing rather than hiding: when Mathlib
moves, `--rebuild`; the incremental path is for the common case, which is that
nothing moved at all and the whole command is free.

Reading is streamed, not slurped. A dump is parsed a batch of lines at a time
off a 1 MiB buffered reader and handed straight to SQLite, so peak memory is a
property of the batch rather than of the corpus — which matters, because the
reason to index a library is that it is large. Parsing the 231 MB Mathlib dump
in one piece held the text and the parsed rows in memory at once and peaked at
**936 MB**; a batch at a time peaks at **246 MB** and costs 3% more wall clock.
The read stays serial and only the parse is spread over the cores: reading off a
warm page cache was never the expensive half.

The dump itself never passes through `dt` at all. `lake env lean` writes the
file, and `dt` runs it with `status()` rather than `output()` — capturing a
subprocess that emits 231 MB is the same mistake one level up.

`--force` re-indexes everything without deleting the file. `--rebuild` deletes
it, which is also what a schema change requires — the index carries a version,
and a database written by a different build is refused rather than read wrong:

```
$ dt status
dt: this index was written by a different version of dt (schema 0, this build
    expects 1); run `dt index --rebuild`
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
