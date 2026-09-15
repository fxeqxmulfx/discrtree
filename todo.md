# todo

Shortcomings found while using `dt` on real work. Newest first.

## Re-indexing after one edit costs 37 s, and 36 of them are spent on work that was already done

Found 2026-09-15, dt 0.8.1, on a Lean project of my own (1864 declarations,
Mathlib and Batteries beside it). Editing a `.lean` file and asking `dt` about
it again means `dt dump project && dt index`, and that is the loop a developer
runs all day:

    $ dt dump project
    real    0m23.057s
    $ dt index
    real    0m13.856s

Both numbers are almost entirely fixed cost, and neither is about the 1864
declarations that changed.

The dump, measured by asking for a prefix that matches nothing:

    DISCRTREE_MODULES=Nope         22.01 s
    DISCRTREE_MODULES=Transformer  23.09 s

So elaborating the whole project is one second; the other twenty-two are
`workList` folding over `env.constants` -- every constant `import Mathlib`
brought in, four hundred thousand of them -- and calling `keep` and
`moduleOf` on each to decide it is not wanted. The environment already knows
the answer structurally: `env.header.moduleNames` says which modules match the
prefix, and `moduleData[i].constNames` lists exactly their declarations. Test
four hundred module names instead of four hundred thousand constants.

The index, measured statement by statement against a copy of the database:

    INSERT INTO decl_fts(decl_fts) VALUES('rebuild')   5.90 s
    INSERT INTO decl_fts(decl_fts) VALUES('optimize')  1.00 s
    ANALYZE                                            1.48 s
    DROP INDEX uses_const                              1.31 s
    CREATE INDEX uses_const ON uses(const, decl_id)    5.33 s

That is 15 s of the 14 measured, so inserting the rows themselves is noise.
Every one of these is right for the load they were written for -- Mathlib, 326
000 rows at once -- and wrong for a load that replaces one row in two hundred.
`decl_fts` is an external-content table, so it can be maintained in place:
`'delete'` with the old column values before `clear_source`, plain inserts
after. The side index does not have to come down for 1864 rows, and `ANALYZE`
has nothing to learn from a 0.5 % change.

The fix is one decision made twice: a load that replaces a small share of the
index maintains it, and a load that replaces most of it rebuilds. The
threshold is not a tuning knob to expose -- it is the point where rebuilding
becomes cheaper, and the index knows the row counts on both sides of it.

Expected after: 2-3 s for the dump (the 2.2 s `import Transformer` floor is
irreducible, and the project's own elaboration is the second), and well under
a second for the index. Thirty-seven seconds to four.

Fixed 2026-09-15 in dt 0.9.0. Measured on the same project, same machine:

    dt dump project   23.06 s -> 3.45 s
    dt index          13.86 s -> 0.64 s

The dump asks the modules instead of the constants. `workList` walks
`header.moduleNames` with `matchesPrefix` and takes the declarations of the
modules that match out of `header.moduleData`, which also makes `moduleOf`
dead: the module is now what the loop is standing in, not something to look
up per constant. The rows are the same rows -- 1872 names, every field equal,
checked against the dump the old walk had just written.

The index decides once per source and can change its mind once per batch. A
load that replaces less than one row in sixteen keeps the side index up,
deletes the rows it is replacing out of `decl_fts` before `decl` forgets what
they said, inserts the new ones as it goes, and finishes by doing nothing at
all. A load bigger than that -- a Mathlib bump, a rebuild, anything into an
empty index -- takes the path that was always there, and a load that starts
small and turns out big switches to it partway through and lets the rebuild
repeat the little it had maintained.

What makes this safe to leave on is that the text index can be asked: FTS5
checks an external-content index against the table it indexes, and
`integrity-check` over all 390 387 rows passes after a maintained load. A test
pins it, and another pins the decision itself -- `sqlite_stat1` still holds
the numbers the last bulk load wrote, which is how a maintained load proves it
did not ANALYZE.

The remaining 3.45 s is 2.2 s of `import Transformer` and a second of
elaborating the project, so the loop is now within a factor of two of the
floor. Cutting the floor means keeping a Lean process alive between dumps,
which is a different program.

## `find`, `show` and `deps` answer from a stale source without saying so

Found 2026-09-13, dt 0.5.0, on a Lean project of my own. Fixed 2026-09-13 in
dt 0.5.0. The other half of the entry below, which `dt status` alone does not
cover, and which the entry below records the repair for.

`dt status` now names a stale `local` source, and the revision moves in both
directions — touching one `.olean` marks it `stale`, restoring the mtime clears
it. The searches do not consult that:

    $ touch .lake/build/lib/lean/Transformer/ALM/SoftmaxIndex.olean
    $ dt status | grep project
    project  local  true  true  784  4m ago  62fdf15 stale
    $ dt find --name hullProbe --source project
    Transformer.ALM.hullProbe  def  Transformer.ALM.HullIndex
    ...

Four results, nothing on stderr, exit 0. `show` is the same. So the check exists
in the command nobody runs before a search, and is absent from the three that
produce the wrong answer — which is the shape the original entry was about: a
stale index answers confidently, and the confidence is what does the damage.

One line on stderr is enough, and stderr specifically, so that piping a result
list into anything is unaffected:

    dt: project is stale (indexed at 62fdf15, now 9ab0d31); dt dump project && dt index

It belongs on any command that reads rows from a source — `find`, `show`,
`deps`, `dup`, `add` — and should name only the sources the answer actually came
from, since a Mathlib search is not compromised by a stale project.

## `dt status` cannot tell that a `local` source has gone stale

Found 2026-09-13, dt 0.4.0, on a Lean project of my own. Fixed 2026-09-13 in
dt 0.5.0, for `dt status`; the searches still do not consult it, which is the
entry above.

`dt status --help` says each source "reports the revision it was indexed from
next to the one it is at now. A source that has moved since is named, because a
stale index answers confidently and wrongly." That holds for `git` and `lake`
sources, which have a revision. A `local` source has none, so its revision
column is `-` and nothing is ever compared:

    source   kind   elaborated  importable  declarations  indexed  revision
    project  local  true        true                 718  2m ago   -

The project had 784 declarations at that moment. Six modules committed since the
last `dt dump` were missing, and `dt find --name hullProbe` answered `no match`
— the exact failure the help text names, and the one source where it is
guaranteed to happen, because the local source is the one that changes every
commit. The remote corpora, which change monthly, are the ones being watched.

`no match` is worse here than a wrong hit: it reads as "Mathlib has no such
lemma, write it yourself", and the name searched for was in the project all
along.

A revision for a `local` source need not involve Lean. The dump already walks
the `.olean` tree; the newest mtime in it, or a hash of (module path, mtime,
size) over that walk, is a revision in the same sense as a git SHA — cheap to
recompute at status time, and it moves exactly when a rebuild has happened:

    project  local  true  true  784  1h ago  4f21c8e (now 9ab0d31, stale)

The same comparison belongs in `find`, `show` and `deps` as a one-line warning
on stderr when the source a result came from is stale, since those are the
commands whose answer the staleness corrupts, and nobody runs `dt status`
before every search.

Both repairs are in. A `local` source is fingerprinted by hashing (module path,
size, mtime) over every `.olean` under `.lake/build/lib`, which is a revision in
the same sense as a git SHA: the dump reads the build, so the build is what has
to have moved for the index to be behind. It has to be the build and not the
`.lean` files, or an edit nobody has compiled yet would report a staleness that
re-dumping would not fix.

`dt status` prints the proposed line as written, both revisions rather than the
word `stale` on its own. That was the other half of the same defect: the help
promised "the revision it was indexed from next to the one it is at now" and the
table had only ever shown the first of the two.

    project  local  true  true  784  1h ago  4f21c8e (now 9ab0d31, stale)

`find`, `show` and `deps` compare the same revisions and warn on stderr:

    dt: `project` moved since it was indexed; this answer may be out of date
        — re-run `dt dump project` and `dt index`

A result with rows is checked against the sources those rows came from. A result
with no rows is checked against every source, because `no match` names no
sources and is the answer the warning exists for. `dt status` names the repair
that fits: an elaborated source is read from the build by `dt dump`, a text
source from the checkout by `dt fetch`, and printing both left the reader to
work out which half applied to them.

The revision appears on the next `dt dump` and `dt index`. An index built by an
earlier `dt` has no revision recorded for its local source, and nothing can
recover what the build was when that dump was taken.

## `dt show` prints the sibling's attribute block for `to_additive` declarations

Found 2026-09-13, dt 0.2.0, on Mathlib. Fixed 2026-09-13 in dt 0.3.0.

    dt show Finset.sum_image

printed

    Finset.sum_image
      theorem  Mathlib.Algebra.BigOperators.Group.Finset.Basic:92-94

    @[to_additive (attr := simp) /-- If a function is injective on a finset, sums over the original
    finset or its image coincide.
    See also `sum_image_of_pairwise_eq_zero` for a version with weaker assumptions. -/]

The statement never appears. `Finset.sum_image` has no source of its own: it is
generated by `to_additive` from `Finset.prod_image`, declared at lines 95-96,
and the range 92-94 is the *attribute block* that sits above the generating
declaration. So the lines shown belong to a different declaration and stop
exactly where the useful part starts.

This is not rare — a large part of Mathlib's `Finset`/`List`/`Multiset` additive
API is generated this way, and those are the lemmas a shape search lands on
most often. Having to fall back to `sed -n '80,96p'` on the Mathlib file is the
one thing `dt show` exists to prevent.

Both of the suggested repairs are in:

    Finset.sum_image
      theorem  Mathlib.Algebra.BigOperators.Group.Finset.Basic:92-94
      generated inside Finset.prod_image:90-97; `dt show Finset.prod_image` has the source

    ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst : AddCommMonoid M] ...

The test is textual and needs no Lean: the lines are the declaration's own only
if a header at column zero names it. If they do not, the declaration whose range
contains them is the one that generated it, and the walk continues outward while
the container is generated too — `MonoidHom.mk` sits inside the projection
`MonoidHom.toMulHom`, which sits inside `structure MonoidHom`.

The other attributes behave the same way and are covered by the same rule.
Sampling 250 random Mathlib rows: 29 were generated, and all 29 were classified
correctly — `to_additive` and `to_dual` twins, `@[simps]` output
(`Equiv.funUnique_symm_apply`), `@[ext]` output (`Finset.ext_iff`), structure
fields, constructors and parent projections, inductive eliminators, and `alias`.
None of the other 221 was misread as generated; the five whose source never
mentions their name are anonymous instances, whose name Lean generated but whose
lines are genuinely theirs.

`dt add` had the same defect and got the same fix: it copies the generating
declaration, once for both halves of a pair, because an attribute block vendored
with nothing under it is a file that does not compile.

## The other lake packages are not indexed, and nothing says so

Found 2026-09-14, dt 0.5.0, on a Lean project of my own. Fixed 2026-09-15 in
dt 0.6.0.

A project's `discrtree.toml` names Mathlib as a `lake` source and stops there,
so everything Mathlib itself is built on -- `batteries`, `aesop`, `Qq`,
`plausible`, `Cli`, `importGraph` -- is invisible to `find` and `show`, even
though every declaration in them is importable from the project without adding
a dependency.  In `transformer` that is 1 161 + 325 936 + 58 674 rows indexed
and all of Batteries missing.

It fails silently, which is the part worth fixing.  Looking for the red-black
depth bound:

    $ dt find --name Balanced --in Batteries
    no match: --in Batteries matches nothing on its own
    $ dt show Batteries.RBNode.Balanced
    Batteries.RBNode.Balanced is not in the index; try `dt find --name Balanced`
    $ dt find --name Balanced
    Ordnode.BalancedSz  def  Mathlib.Data.Ordmap.Invariants
    ...

Three answers, none of which says "Batteries is not a source of this index".
The last one is the worst: it returns ten Mathlib rows, so it reads like a
complete answer to a question it did not search.  The declaration wanted was
`RBTree.RBNode.WF.depth_bound`, and it was found by `grep -rn` over
`.lake/packages/batteries`, which is the one thing `dt` exists to prevent.

Two repairs, both small:

* `dt status` lists the directories under `.lake/packages` that are not
  configured as sources, the way it already lists the sources that are stale.
  That is where a user looks when an answer seems thin.
* `--in <prefix>` that matches no indexed module says so, instead of reporting
  that the filter matched nothing.  The two cases are different: a prefix
  inside an indexed source that happens to be empty, and a prefix belonging to
  a source that was never indexed.

The third repair is not dt's: a project that wants those packages can add them
as `lake` sources itself.  But it has to know they are missing first.

Both are in. `dt status` ends with the packages the build resolved that no
source points at, read off `.lake/packages` and not off `lake-manifest.json` --
the manifest says what was resolved and the directory holds what was fetched,
and an `import` line resolves against the second:

    not indexed: aesop, batteries, Cli, importGraph, LeanSearchClient,
                 plausible, proofwidgets, Qq
      -- lake packages the build resolved; add one as a `lake` source to search it

And an empty result from a prefix one of them provides names the package
instead of blaming the prefix:

    $ dt find --name Balanced --in Batteries
    no match: `Batteries` is in the lake package `batteries`, which is not a
    source of this index; add it to discrtree.toml and re-run `dt dump
    batteries` and `dt index`

A package is traced back to from a prefix by the one part of its layout that is
readable without running Lake: a library root is an `X.lean` sitting beside a
directory `X`. Half of these declare their libraries in `lakefile.lean`, which
is a program and not data. A package whose layout does not follow the
convention is still listed by `dt status`; it just cannot be reached from a
prefix.

The entry says two repairs and there were three. `dt show` had the same dead
end -- the session above went `show`, then `find`, then `grep`, and repairing
only `--in` leaves that loop intact -- so a missing name whose namespace belongs
to an unindexed package now names the package rather than suggesting `dt find
--name`, which from a corpus that was never dumped can only return the same
nothing or a page of Mathlib near-misses that read like an answer.

What is still not done is the third repair the entry rules out, and for the
reason it gives: adding a source is the reader's call. A tool that guessed
would dump gigabytes nobody asked for.

## Lean core is not a source, and nothing says so

Found 2026-09-15, dt 0.6.0, on a Lean project of my own. Fixed 2026-09-15 in
dt 0.7.0.

`Int.add_one_le_iff` is `theorem add_one_le_iff {a b : Int} : a + 1 ≤ b ↔ a < b`
in `Init/Data/Int/Order.lean` of the toolchain itself. Asked for it:

    $ dt show Int.add_one_le_iff
    dt: Int.add_one_le_iff is not in the index; try `dt find --name add_one_le_iff`

    $ dt find --name add_one_le_iff
    PNat.add_one_le_iff / ENat.add_one_le_iff / Cardinal.natCast_add_one_le_iff / ...
    10 shown, more match; refine or --limit

Ten near-misses over `PNat`, `ENat`, `Cardinal` and `Ordinal`, and the `Int` one
is not among them at any `--limit`, because it was never dumped. The same
happens for `Int.emod_emod_of_dvd` (`no match`) and for every other `Int`, `Nat`,
`List` or `Array` lemma that core proves and Mathlib only uses.

This is the entry above -- "The other lake packages are not indexed, and nothing
says so" -- one level down, and the repair it shipped does not reach here. That
repair traces an unfound prefix back to a *lake package* listed by `dt status`.
Core is not a lake package and `dt status` does not list it at all, so
`Int.add_one_le_iff` falls through to the generic suggestion, which from a
corpus that never held it returns the page of Mathlib namesakes above -- the
failure that entry set out to remove, reached by the one route it does not
cover.

Two things to do, and the second is the one that matters:

* `dt status` should name the toolchain the index was built against and say
  whether its `Init`/`Std` were dumped, the way it names the lake packages that
  were not. A reader who sees `core: not indexed` stops trusting a `no match`
  under `Int.`, `Nat.`, `List.` or `Array.` and greps; a reader who sees nothing
  concludes the lemma does not exist.
* A missing name whose root namespace is one core owns (`Int`, `Nat`, `List`,
  `Array`, `Option`, `String`, `Fin`, `BitVec`, ...) should say so, exactly as an
  unindexed package's prefix now does, rather than suggesting `--name`.

Adding core as a source is a third thing and, like adding a lake package, the
reader's call: `~/.elan/toolchains/<tc>/lib/lean/library` is dumpable and the
declarations are elaborated, but nobody asked for them. Saying they are absent
costs nothing and is what the two sessions that hit this actually needed.

Both are in, and the second took a list rather than a directory walk. A lake
package announces itself by sitting under `.lake/packages`, so what it provides
can be read off disk; core ships inside the toolchain, and the modules that
would say what it declares are exactly the ones nobody dumped. So it is written
down in `domain/lean_core.rs`, as two lists that are deliberately not the same
one:

* `ROOTS` -- `Init`, `Std`, `Lean` -- what a source would have to import, and
  what `--in` is asked with.
* `NAMESPACES` -- `Int`, `Nat`, `List`, `Array`, ... -- what a declaration name
  starts with.

`Int.add_one_le_iff` is declared in module `Init.Data.Int.Order`, so the module
root is `Init` and the namespace root is `Int`, neither derives from the other,
and a name is all `dt show` has to go on. The namespace list is held to the
types core defines and proves about; `Function` and `Set`, which both libraries
declare in heavily, are left out, because an explanation that fits every missing
name explains nothing.

`dt status` now names the toolchain in its header either way, and calls out an
absent core beside the packages:

    index: .lake/discrtree/index.db
    toolchain: leanprover/lean4:v4.33.1
    ...
    not indexed: Lean core (leanprover/lean4:v4.33.1)
      -- Init, Std, Lean live in the toolchain, not under `.lake/packages`; a
         `no match` under `Int.`, `Nat.`, `List.` or `Array.` is often theirs

"Core is indexed" is printed too, because it answers "why did that not match"
as squarely as its opposite. Whether it is indexed is decided by what a source
imports rather than by where it points: a dump of core has to say `import
Init`, while the path may be elan, a source tarball or a checkout of lean4.

The claim `dt show` makes is weaker than the one it makes for a package, and
deliberately:

    dt: Int.add_one_le_iff is not in the index, and `Int` is a namespace Lean
    core declares in; core (leanprover/lean4:v4.33.1) is not a source of this
    index, so `--name` cannot reach it either

A package owns a directory and its namespace is its own; `Int` is a namespace
core and Mathlib both declare in, so the honest claim is about the namespace and
not about the declaration. That is enough to stop a reader concluding the lemma
does not exist, which is the whole failure. Neither message offers a `dt dump`
line, because core is no directory a source can be pointed at in one line, and a
command that does not work is worse than none.

The port grew to fit: `Packages` is now `Build` -- what the build can import, as
against what the index holds -- with `unindexed()` for the packages,
`toolchain()` for core, and the two questions separated, `module(prefix)` and
`declaring(name)`, because for a package they have the same answer and for core
they do not.

### Follow-up: `find --name` and `deps` do not say it

0.7.0 ships the note on `dt show` and the `dt status` line, and both are
exactly right:

    $ dt show Int.add_one_le_iff
    dt: Int.add_one_le_iff is not in the index, and `Int` is a namespace Lean
    core declares in; core (leanprover/lean4:v4.33.1) is not a source of this
    index, so `--name` cannot reach it either

The other two entry points still end where they did:

    $ dt find --name Int.emod_emod_of_dvd
    no match

    $ dt deps Int.add_one_le_iff
    dt: Int.add_one_le_iff is not in the index

Both were handed a qualified name whose root namespace is core's, which is
the one case the note can be derived from, and the `show` message even
promises what `--name` will do -- so a reader who follows that sentence to
`find --name` gets the bare `no match` the note was written to prevent. The
unqualified `dt find --name add_one_le_iff` cannot be repaired this way and
should not be: there is no namespace in it to read.

Fixed 2026-09-15 in dt 0.8.0. The sentence itself moved into the domain of
the answer: `Missing::about(name)` writes it once, and `dt show` and
`dt deps` both print exactly that, so the two commands that dead-end on a
qualified name can no longer disagree. `dt deps` had no way to ask -- it
held only a repo and a workspace -- and now takes a `Build` it consults on
the miss alone.

`dt find --name` asks only when the value it was handed is qualified, and
only after the search has come back empty, so the common fragment search
pays nothing. What it says is not what `show` says, because what it was
asked is not a declaration: an empty search reports the *namespace* it
could not reach, not the name typed into it, and `Empty::NotIndexed` now
carries an `Asked` to keep `--in Init.Data.Int` (a module of core) and
`--name Int.emod_emod_of_dvd` (a namespace core declares in) phrased apart.
The unqualified search stays a bare `no match`, pinned by a test.

The one promise that had to be withdrawn is the one this entry quotes: the
`show` message no longer says `--name` cannot reach it either, because now
`--name` answers for itself. It says no search here can reach it.

## `dt index` has no `--source`, but the staleness hint implies one

`dt index --source project` is rejected with `Usage: dt index --force`, while
the staleness warning at the bottom of a `find` result says to "re-run
`dt dump project` and `dt index`".  Two asymmetries in one place: `dump` takes
a source name positionally and `index` takes none, and the warning names the
two-command sequence rather than a single `dt refresh project` that would do
both.  Re-indexing one source after a few commits is the commonest maintenance
action there is; it should be one command, and the flag that `dump` accepts
should be accepted by `index` too (even as a no-op) so the obvious guess works.

Reported from the transformer repo, 2026-09-15.

Fixed 2026-09-15 in dt 0.10.0, and not as a no-op: `dt index project`
indexes that source and leaves the others where they are, which is what the
word narrows to mean once it can be narrowed.  `--source` is accepted
everywhere the positional is -- `dump`, `scan`, `fetch`, `index`, `refresh` --
and hidden from `--help`, so the guess works without teaching a second
spelling to anyone who never made it.  `--rebuild` refuses a source name
outright rather than narrowing: it deletes the database, so "rebuild this one
source" would read as the opposite of what it does.

`dt refresh` is the command the warning was describing.  With a name it reads
that source again and indexes it -- from the build if the source is
elaborated, from the checkout if it is text, which is the whole reason the
advice used to come in two flavours -- and it does so whether or not the
source looks stale, because naming one means knowing something the timestamps
do not.  With no name it refreshes exactly the stale sources, never all of
them: a bare word that can start a 25-minute Mathlib dump is a word nobody
can type with confidence.  The re-index is forced, since the fingerprint it
would consult is one this command just rewrote.

Both messages now name it.  The `dt:` line says "re-run `dt refresh project`",
and `dt status` prints one `behind:` line for every stale source instead of
splitting them across `behind the build:` and `behind the checkout:` -- that
split existed only to tell the reader which of two commands applied to them,
and there is one command now.

## Lean core is not indexable, and `List` is where that hurts

`dt show List.chain_append` answers that `List` is a namespace core declares
in and core is not a source of this index — clear, and a dead end.  Today's
work needed `List.IsChain` (renamed from `Chain'` in Mathlib v4.33.1) and its
append/split lemmas; the split ones are Mathlib's and dt found them, but
`List.head?`, `List.getLast?` and their whole API are core's, so every question
about them fell back to grep over `.lake/packages`.  A `kind = "core"` source
pointing at the toolchain's `src/lean` would cover `Init.Data.List`,
`Init.Data.Option` and `Init.Data.Nat`, which between them are most of what a
data-structure proof reaches for.

Reported from the transformer repo, 2026-09-15.

Fixed 2026-09-15 in dt 0.11.0.  `kind = "core"` is a source configured by
kind alone: no path, no url, no root.  What it imports (`Lean`, which is what
pulls `Init` and `Std` in with it) and which module roots it keeps (all three)
are facts about Lean rather than choices, and asking the reader for them would
be asking them to know the trick -- that a `lake` source pointed at `Init`
would have worked all along.  It is in the `dt init` template as a live
source, not a commented one, because the reader who never edits that file is
exactly the reader who will otherwise grep `.lake/packages` for `List.head?`.

Nothing new had to be built to dump it.  The environment walk added in 0.9.0
reads `env.header.moduleData`, and core's modules are in there in every build
-- the project already imports them transitively -- so `dt refresh core` costs
one import of `Lean` and the same per-module walk every other source pays:
97 609 declarations in 20 s of dumping and 23 s of indexing, 84 MB of JSONL.
On the transformer project the index went from 390 408 rows to 488 017.

Core has no directory this tool put on disk, and `dt show` needs one to print
source text.  It is found rather than placed: elan lays its toolchains out
under `$ELAN_HOME/toolchains/<name with its separators folded>`, which is one
directory test, and when that misses `lean --print-prefix` is asked -- from the
project root, because run anywhere else it resolves elan's *default* toolchain
and can start a three-gigabyte download of a toolchain nobody wanted.  Under
either answer `src/lean` holds `Init/Data/List/Basic.lean`, so the module-to-
path rule every other source uses works unchanged, and `dt show List.head?`
prints the import line, the docstring and the body.

Core's revision is the toolchain name.  That is not a placeholder: core moves
when `lean-toolchain` moves and at no other time, so a bump makes `dt status`
report core as behind and a bare `dt refresh` re-dump it -- the same machinery
a Mathlib bump gets, for the same reason.

The messages that used to dead-end now carry the repair.  `Missing::fix()` is
one sentence, written once and printed by `dt show`, `dt deps`, the `no match`
line and `dt status` alike: for a package, add it and `dt refresh <pkg>`; for
core, add a source with `kind = "core"` and `dt refresh core`.  The old
comment explaining that core had no command to offer has gone with it.

## A bare `dt refresh` stops at the first source it cannot read

A toolchain bump is the moment every source in the index goes stale at once,
and it is the one moment `dt refresh` with no name cannot do its job.  The
project's own `.olean`s are the first thing the bump invalidates, so
`dump_project.lean` fails with `incompatible header`, and the command exits
there: `mathlib`, `batteries` and `core` are left on the previous toolchain's
declarations, which is exactly the index a `Finset.prod_le_prod` question is
about to be asked of.

The order makes it worse than a coin flip -- the source most likely to fail is
the local one, and it is the one that is refreshed first.  A source that fails
should be reported and skipped, with the others still refreshed and a non-zero
exit at the end naming what was missed.  As it stands the repair is to know
that `dt refresh <each other source>` exists and to type it four times.

Reported from the transformer repo, 2026-09-15, bumping Lean v4.33.1 to
v4.34.0.

Fixed 2026-09-15 in dt 0.12.0.  Every selected source is read, each failure is
reported where it happens rather than in the summary, the sources that were
read are indexed, and the command exits non-zero naming what was left alone:

    $ dt refresh
    dt: `nope`: lake env lean failed for source `nope` (exit 1); `Nope.olean`
        was built by Lean 4.33.1 and lean-toolchain says 4.34.0 -- run `lake
        build` first
    toy: dumped to .discrtree/jsonl/toy.jsonl
    toy: 1 declarations indexed
    index: .discrtree/index.db (2 rows)
    dt: 1 of 2 sources could not be read and were left as they were: nope
    $ echo $?
    1

Reproduced on a two-library toy project rather than on the repo that reported
it, which had already been repaired by hand: one library's `.olean` was given a
previous toolchain's header, which is the whole of what a bump does to a build,
and both sources went stale together because a `local` source is fingerprinted
by the build they share.

`dt refresh <name>` keeps the shape it had.  One name, one failure, nothing
else attempted: the reason is the whole answer, and a summary over a list of
one would only bury it.

What can be tested without a Lean on the machine is the decision, so that is
what the loop was made into -- a function over the targets that takes the
reading half as a closure and hands back what was read and what was not.  Two
tests pin it: the first failure does not stop the rest, and every failure is
reported rather than only the first.

## After a toolchain bump `dt refresh mathlib` fails on a file the cache never ships

`lake exe cache get` fetches 8 906 `.olean`s and not `Mathlib.olean`, the
top-level module that imports them all.  Nothing in a normal build needs it --
a project imports `Mathlib.Data.List.Chain`, never `Mathlib` -- so the stale
one from the previous toolchain is left sitting on disk, and `dump_mathlib.lean`
is the one consumer that imports `Mathlib` wholesale:

    failed to read file '.../Mathlib/.lake/build/lib/lean/Mathlib.olean',
    incompatible header
    dt: lake env lean failed for source `mathlib` (exit 1); the script is at ...

The message points at the dump script, which is not where the repair is.  The
repair is `lake build Mathlib` in the project root -- about three minutes with
every dependency already cached -- and dt is in a position to know that: the
header it could not read names the toolchain that wrote it, and comparing that
to `lean-toolchain` is the whole diagnosis.  A `Missing::fix()` sentence for
this case would say it in one line, the way the `kind = "core"` one now does.

Worth considering whether the dump needs `Mathlib.olean` at all.  The
environment walk added in 0.9.0 reads `env.header.moduleData`, and the module
list could come from `Mathlib.lean`'s import lines read as text rather than
from importing the module -- which would also drop three minutes off the first
refresh after every bump.

Reported from the transformer repo, 2026-09-15, bumping Lean v4.33.1 to
v4.34.0.

