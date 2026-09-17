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
misremembered name costs one line, not the other four lookups.  A name as the
source writes it inside its namespace, `countP_range'_add` for
`Transformer.CRASP.countP_range'_add`, is shown when it ends one declaration,
or one of the project's own.

`dt skill` prints the whole interface in 32 lines — the rules that are not
guessable, and nothing else. It is meant to be read once by an agent instead of
eleven `--help` screens, and `dt skill --install` drops it into
`.claude/skills/discrtree/SKILL.md` so it is loaded only when it is needed. The
text is compiled into the binary from that same file, so the printed copy and
the shipped one cannot drift apart.

## An empty answer says which repair it needs

`no match` is the most expensive line `dt` can print, because on its own it
does not say what to do next. Four situations produce it and they need
different repairs:

```
$ dt find --name exp --in Analysis
no match: --in Analysis matches nothing on its own

$ dt find --name exp --uses Finset.sum --in Mathlib.Order
no match: every condition matches on its own; drop one

$ dt find --name Balanced --in Batteries
no match: `Batteries` is in the lake package `batteries`, which is not a source
of this index; add it to discrtree.toml and re-run `dt dump batteries` and
`dt index`
```

The first is a condition to edit — Mathlib's modules begin `Mathlib.`, so
`Analysis` is not a prefix of any of them. The second is a condition to drop.
Guessing between them costs a search either way; asking each condition on its
own costs one row each, and only when the search has already failed.

The third is neither, and that is why it is told apart: `Batteries` is spelled
correctly and there is nothing to drop. It is the index that is smaller than
the build, and the repair is a source, not a flag. `dt show` answers a missing
name the same way rather than with `try dt find --name`, which from an unindexed
corpus can only return the same nothing or a page of Mathlib near-misses that
read like an answer. The toolchain's own library answers there too, with a
weaker claim and no `dt dump` line, because core is no directory a source can be
pointed at in one line:

```
$ dt show Int.add_one_le_iff
dt: Int.add_one_le_iff is not in the index, and `Int` is a namespace Lean core
    declares in; core (leanprover/lean4:v4.33.1) is not a source of this index,
    so `--name` cannot reach it either
```

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
project        local   true         true                  784  2h ago   4f21c8e (now 9ab0d31, stale)
mathlib        lake    true         true               325936  2h ago   0df444a
flt            git     false        false               58674  2h ago   aa2d8b3

behind the build: project — re-run `dt dump` and `dt index`
```

A lake dependency's revision comes from `lake-manifest.json`, which is what the
next `lake build` will honour, and a text source's from the checkout's `HEAD`.
A source that has moved shows both revisions rather than the word `stale` alone:
one of them says a re-dump is due, the pair says how far behind and against
what, which is what `git log A..B` wants. A source with no revision to read is
reported as `-` and never as stale: a warning that is always on is a warning
nobody reads.

The project itself has neither. Nobody pins it, and its working tree is ahead of
its last commit by definition — that is what working on it means. So its
revision is a hash of (module path, size, mtime) over every `.olean` under
`.lake/build/lib`, which moves exactly when a rebuild has happened. It has to be
the build rather than the `.lean` files, because the build is what `dt dump`
reads: an edit nobody has compiled yet would otherwise report a staleness that
re-dumping would not fix.

This is the source where staleness is guaranteed rather than occasional. Mathlib
is bumped monthly and the project changes every commit, so the corpus being
watched was the one that moves least. `find`, `show` and `deps` therefore make
the same comparison and warn on stderr:

```
dt: `project` moved since it was indexed; this answer may be out of date — re-run `dt dump project` and `dt index`
```

A result with rows is checked against the sources those rows came from; a result
with no rows is checked against every source, which is both the case the warning
exists for and the case where checking is free. `no match` from a stale index is
worse than a wrong hit — it reads as "upstream has no such lemma, write it
yourself" when the lemma was in the project all along.

`dt index` leaves alone any source whose input has not changed since it was
indexed. The input is the dump for a compiled source and the checkout for a
text one, fingerprinted by size and mtime in the first case and by revision in
the second — so a Mathlib bump that has not been dumped again changes nothing,
which is correct, because the index is built from the dump.

| | |
| --- | ---: |
| `dt index` with nothing changed | 0.04 s |
| `dt index` after one source moved | 98 s |
| `dt index --rebuild` | 75 s |

Re-indexing one large source in place costs *more* than starting over, because
the rows have to be deleted before they are written and the text index is
rebuilt either way. That is worth knowing rather than hiding: when Mathlib
moves, `--rebuild`; the incremental path is for the common case, which is that
nothing moved at all and the whole command is free.

Most of a rebuild used to be index maintenance rather than work. Sixteen
million side-table rows go in, and three indexes over them had to be kept in
step — `uses(const, decl_id)`, `uses(decl_id)`, `dep(decl_id)`, together 383 MB
of a 1.2 GB file. The rows arrive in declaration order, which is not the order
any of those trees is sorted by, so past the point where they outgrow the page
cache every insert is a page fault. That is why 54 of the old 141 seconds were
system time rather than user time.

Two of the three are now gone. Both side tables are `WITHOUT ROWID` with
`decl_id` leading the primary key, so they *are* the index on `decl_id`:
reading a declaration's constants and deleting a source's rows are range scans
over rows that are already adjacent, and a load appends to the right-hand edge
in order. The third, `uses_const`, answers the opposite question — which
declarations mention a constant — and nothing about indexing needs it, so a
load drops it and `finish` builds it back in one pass over rows already on
disk, which is sorted work.

| | before | after |
| --- | ---: | ---: |
| `dt index --rebuild` | 141 s | **75 s** |
| of which system time | 54 s | 17 s |
| index on disk | 1.2 GB | 1.1 GB |

Clustering rather than indexing is the part that is easy to get wrong.
`clear_source` runs *between* loads, when `uses_const` is down; a first attempt
kept the tables as they were and dropped all three indexes, and re-indexing one
source in place went from two minutes to over eighteen, because the delete had
lost the index it searched by.

Reading is streamed, not slurped. A dump is parsed a batch of lines at a time
off a 1 MiB buffered reader and handed straight to SQLite, so peak memory is a
property of the batch rather than of the corpus — which matters, because the
reason to index a library is that it is large. Parsing a dump in one piece held
the text and the parsed rows in memory at once and peaked at **936 MB** on the
231 MB dump it was measured against — four times the file. A batch at a time
peaks at **356 MB** against a dump that has since grown to 503 MB, and 64 MB of
that is a page cache the loader asks for on purpose. The read stays serial and
only the parse is spread over the cores: reading off a warm page cache was
never the expensive half.

The dump itself never passes through `dt` at all. `lake env lean` writes the
file, and `dt` runs it with `status()` rather than `output()` — capturing a
subprocess that emits 503 MB is the same mistake one level up.

`--force` re-indexes everything without deleting the file. `--rebuild` deletes
it, which is also what a schema change requires — the index carries a version,
and a database written by a different build is refused rather than read wrong:

```
$ dt status
dt: this index was written by a different version of dt (schema 1, this build
    expects 2); run `dt index --rebuild`
```

## What the index does not cover

A `discrtree.toml` names Mathlib and stops there. Everything Mathlib is built on
— batteries, aesop, Qq, plausible, Cli, importGraph — is then importable from
the project without adding a dependency, and invisible to every search. The
index cannot report that on its own: a corpus nobody dumped leaves nothing
behind to find. The directory the build resolved is the only evidence there is,
so `dt status` reads it:

```
not indexed: aesop, batteries, Cli, importGraph, LeanSearchClient, plausible, proofwidgets, Qq
  — lake packages the build resolved; add one as a `lake` source to search it
```

A package is a directory under `.lake/packages` that no source's `path` points
at; the library it provides is an `X.lean` sitting beside a directory `X`, which
is the convention an `import` line relies on and the only part of a package
readable without running Lake — half of these declare their libraries in
`lakefile.lean`, which is a program, not data.

Naming them is the whole repair. Which ones are worth a dump is the reader's
call: Batteries is a minute and a useful corpus, and a tool that decided for
them would be spending an hour on packages nobody searches.

Under all of them is the corpus with no directory to be listed from at all.
`Int.add_one_le_iff` is proved in `Init/Data/Int/Order.lean` of the toolchain
itself, so `--name add_one_le_iff` answers with ten `PNat`, `ENat` and `Cardinal`
namesakes and none of them is the one, at any `--limit`. The toolchain is
therefore named either way, and called out when its library is absent:

```
index: .lake/discrtree/index.db
toolchain: leanprover/lean4:v4.33.1
...
not indexed: Lean core (leanprover/lean4:v4.33.1)
  — Init, Std, Lean live in the toolchain, not under `.lake/packages`; a `no match`
    under `Int.`, `Nat.`, `List.` or `Array.` is often theirs
```

What core provides cannot be walked — the modules that would say are exactly the
ones nobody dumped — so it is written down in `domain/lean_core.rs` instead, as
two lists that are deliberately not the same one. `Int.add_one_le_iff` is
declared in module `Init.Data.Int.Order`: the module root is `Init` and the
namespace root is `Int`, neither derives from the other, and a name is all
`dt show` has to go on. The namespace list is held to the types core defines and
proves about; namespaces the two libraries share heavily (`Function`, `Set`) are
left out, because an explanation that fits every missing name explains nothing.

## The dump runs on every core

Indexing Mathlib is a minute. Dumping it was twenty-five, on one core out of
twelve, because the dumper walked the environment and elaborated each
declaration in turn.

It is now one thread per core over a shared environment. The walk stays serial
— it is the cheap part — and collects a work list, which is dealt out and
elaborated in parallel. Nothing here adds a declaration, so every thread starts
from the same `Core.State` and its result state is dropped; there is nothing to
merge back. `DISCRTREE_JOBS` overrides the thread count, which otherwise
follows the hardware concurrency.

| | |
| --- | ---: |
| `dt dump mathlib` on one core | 25:10 |
| `dt dump mathlib` on twelve | **4:06** |

Threads rather than processes, because the environment is the whole expense:
`import Mathlib` by itself is 9 s and **6.9 GB**, so twelve processes would
want 83 GB on a machine that has 30. Twelve threads sharing one environment
moved the peak from 7.31 GB to 7.42 GB — a thread costs its own elaboration
caches and nothing else.

Round robin rather than contiguous blocks, because what a declaration costs is
the size of its proof term, and those cluster by file: contiguous shares leave
one thread alone in `Mathlib.Analysis` long after the rest have finished. Each
thread writes its own file and the parts are concatenated in share order, so
the dump is one file and the same file however many threads wrote it — byte for
byte against the serial dumper, which is how the change was checked.

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
