# todo

Shortcomings found while using `dt` on real work. Newest first.

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
