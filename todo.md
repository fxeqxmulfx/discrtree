# todo

Shortcomings found while using `dt` on real work. Newest first.

## A power that misses as written takes 0.7 s, reading the same rows at every look

Found 2026-09-22, dt 0.58.0, timing the 0.58.0 fix on the same project. A
pattern whose power no row writes as written now takes every look, and each
look reads every row under its conclusion again:

    $ time dt find 'x * x * x * x = _'
    dt: `_ * _ * _ * _` read as `_ ^ 4` — nothing states it as written
    Complex.I_pow_four  theorem  Mathlib.Basic.Complex.Basic
    ...
    real    0m0.727s

`x * x * x = _` takes 0.60 s and `_ = a * a` 0.40 s, against 0.19 s and
0.29 s with dt 0.57.0. A profile of the first puts half of it in reading rows:
the index has the conclusion and not the heads of its arguments, so `_ = _ *
_` reads all 163 000 `Eq` rows to keep the 6564 with a product, and a pattern
with no power does the same: `a + b = b + a` takes 0.14 s. A quarter goes to
the lists of the rows kept, two thirds of them the dependencies of their
proofs, which no search reads. A fifth goes to reading each statement for its
powers, at every look again, and the turned look asks the index what the
first one did.

The right output: the same answers, in the time 0.57.0 took or less.

Seen with dt 0.58.0, 2026-09-22.

Fixed in 0.59.0. Each of the four is answered where it lies. The index keys
the heads of the conclusion's arguments beside the conclusion itself, so
`_ = _ * _` reads the 6564 rows with a product and not the 163 000 `Eq` rows
they are among. A search reads the constants of a row only when the query
names constants -- which is when ranking and `dt dup` look at them -- and
never the dependencies of its proof, which nothing a search does reads. The
rows of a query are kept until something writes to the index, so the turned
look, whose SQL is the first look's because the index keys heads and neither
side, is answered without reading them again. And a statement too short of
multiplication signs to write the power asked for is turned away by its bytes:
71% of those 6564 rows are short of the three `x * x * x * x` needs, and
reading one for its powers costs ten microseconds. Reading what remains got
twice as cheap besides, by lexing and splitting without allocating: 9.9 µs a
statement against 20.2 µs, over all 460 682 of them.

    x * x * x * x = _    0.727 -> 0.150    (0.57.0: 0.191)
    x * x * x = _        0.597 -> 0.133    (0.57.0: 0.191)
    _ = a * a            0.399 -> 0.141    (0.57.0: 0.285)
    ‖x‖ * ‖x‖ = ⟪x, x⟫_ℝ 0.217 -> 0.061    (0.57.0: 0.120)
    a + b = b + a        0.142 -> 0.068    (0.57.0: 0.141)
    0 ≤ a * a            0.036 -> 0.017    (0.57.0: 0.035)

Best of three on the same project, seconds. The answers are unchanged: 25
patterns at two limits print what 0.58.0 printed, and every one of the
460 682 statements of that index reads the same powers as before. An index
written by an earlier dt builds the new one on the first open, which takes
about 0.7 s once and 14.7 MB, and drops the one it replaces.

## A power in a pattern ranks nothing, so `0 ≤ a * a` puts every product before the square

Found 2026-09-22, dt 0.57.0, checking the 0.57.0 fix on the same project. A
square written as a product is matched by its head, `HMul.hMul`, which every
product has, and the rows that write the square are ranked among the rest by
the length of their type:

    $ dt find '0 ≤ a * a'
    Real.sign_mul_nonneg  theorem  Mathlib.Basic.Real.Sign
      ∀ (r : ℝ), 0 ≤ r.sign * r
    Lean.Omega.Int.ofNat_mul_nonneg  theorem  Init.Omega.Int
      ∀ {a b : Nat}, 0 ≤ ↑a * ↑b
    Real.mul_log_nonneg  theorem  Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
      ∀ {x : ℝ}, 1 ≤ x → 0 ≤ x * Real.log x
    ...
    10 shown, more match; refine or --limit

`mul_self_nonneg` is 24th of 45. `0 ≤ a ^ 2` the same way puts `0 ≤ 0 ^ x`
and `1 ≤ 2 ^ n` first and `sq_nonneg` 25th of 42.

And the other way round and the other spelling are second looks, taken only
when nothing matches, so a product that matches by heads never gets them:

    $ dt find '‖x‖ * ‖x‖ = ⟪x, x⟫_ℝ'
    InnerProductGeometry.cos_angle_mul_norm_mul_norm  theorem  Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
      ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] (x y : V),
    1 result(s)

    $ dt find 'x * x * x = _'
    EReal.top_mul_bot  theorem  Mathlib.Data.EReal.Operations
      ⊤ * ⊥ = ⊥
    ...

The product in `cos_angle_mul_norm_mul_norm` is `Real.cos (angle x y) * (‖x‖ *
‖y‖)`; `real_inner_self_eq_norm_mul_norm` states the square with its sides
swapped, and `real_inner_self_eq_norm_sq` as `‖x‖ ^ 2`. The cube answers 2700
products and not `pow_three'`, `a ^ 3 = a * a * a`, which states it the other
way round.

The right output: a row whose statement writes the pattern's power ranks above
one that only shares its head; and a look whose rows all only share it is a
miss to the second looks, which answer when they find the power, with those
rows kept as the answer when they do not.

Seen with dt 0.57.0, 2026-09-22.

Fixed in 0.58.0. A row whose printed statement writes the pattern's powers,
spelled as the pattern spells them and on its side, ranks above one that only
shares their heads: `0 ≤ a * a` puts `mul_self_nonneg` first, and `0 ≤ a ^ 2`
the seven that state `0 ≤ a ^ 2` before `0 ≤ 0 ^ x`, `sq_nonneg` fourth. Rows
that all only share the heads are a miss to the second looks, the relation
turned and then each respelling and its turn, and the first look to find a row
that writes the power answers with those rows alone: `x * x * x = _` answers
`pow_three'` and `pow_three` turned, `‖x‖ * ‖x‖ = ⟪x, x⟫_ℝ`
`real_inner_self_eq_norm_mul_norm` turned. Where no look finds it, the rows
that share the heads stay the answer -- the first look's, or the turned look's
when the first finds none. A pattern that misses as written now takes every
look, at a query each: `x * x * x * x = _` goes from 0.2 s to 0.7 s on
Mathlib.

## A square written `x ^ 2` misses the lemma Mathlib states with `x * x`

Found 2026-09-22, dt 0.56.0, looking for Cauchy-Schwarz against a unit vector,
`⟪x, w⟫² ≤ ‖w‖²`, in the form a proof goal carries it:

    $ dt find 'inner ℝ _ _ ^ 2 ≤ _'
    No match: `inner` is `Inner.inner` in the index — Lean prints an exported
    name without its namespace — and that matches nothing either
    $ dt find '⟪_, _⟫_ℝ ^ 2 ≤ _'
    no match: the shape matches, but nothing of that shape mentions
    `Inner.inner`; ...

The lemma is there, written as a product:

    $ dt find 'inner ℝ _ _ * inner ℝ _ _ ≤ _'
    real_inner_mul_inner_self_le  theorem  Mathlib.Analysis.InnerProductSpace.Basic
      ... ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ

Both answers are literally true, but a square is spelled both ways across
Mathlib (`sq_nonneg` vs `mul_self_nonneg`, `sq_abs` vs `abs_mul_abs_self`), and
a user writing either spelling means both.  The first message also puts the
blame on the resolution of `inner`, which worked; what failed is the `^ 2`.

The right output: match `e ^ 2` against `e * e` as well (and the reverse),
announced on stderr the way the `inner` rewrite is; or at least, on a miss,
retry with the other spelling and name it -- "no match for `_ ^ 2`; as
`_ * _`: real_inner_mul_inner_self_le, ...".

Fixed in 0.57.0. A pattern that finds nothing is asked again with the powers
its sides are written as spelled the other way: `x ^ n`, for any numeral `n`,
as the product of `n` factors `x` in any grouping, and such a product as
`x ^ n` -- all of them at once, then each on its own, and each of those turned
where an equation may be. A row is kept only where its printed statement writes
that power on that side, because the index has `HMul.hMul` for `x * y` too, and
stderr says `` `_ ^ 2` read as `_ * _` — nothing states it as written ``. A
bare word is resolved first and the power respelt in the resolved pattern, so
both patterns above answer `real_inner_mul_inner_self_le`, with `inner` read
as `Inner.inner` in the first. Factors are one term only when written alike
with no `_` in them: `_ * _` and `s.card * t.card` are no squares. A power
inside a side is not respelt. A pattern that misses both ways is diagnosed as
before, the `inner` message included.

The second spelling is a second look, as the other way round is, and a pattern
that finds anything as written gets neither. A product seldom finds nothing,
since `x * x` matches `x * y` by heads: `‖x‖ * ‖x‖ = ⟪x, x⟫_ℝ` answers
`cos_angle_mul_norm_mul_norm`, whose product is no square, and not
`real_inner_self_eq_norm_mul_norm` turned or `real_inner_self_eq_norm_sq`
respelt.

## A `⊆` pattern misses every `Set` and `Finset` lemma, which the index keys by `≤`

Found 2026-09-21, dt 0.55.0, checking the 0.55.0 fix on the same project:

    $ dt find "f '' (s ∩ t) ⊆ _"
    no match: nothing has that shape; those arguments go together under `Eq`
    (881), `LE.le` (134), `Membership.mem` (23)

    $ dt find "f '' (s ∩ t) ≤ _"
    Set.image_inter_subset  theorem  Mathlib.Data.Set.Image
      ... f '' (s ∩ t) ⊆ f '' s ∩ f '' t

Mathlib's `⊆` on `Set` and `Finset` elaborates to `LE.le` and only prints as
`⊆`: of the unhypothesised statements printed with a `⊆`, 1043 have the
conclusion `LE.le` and 69 -- lists, multisets -- `HasSubset.Subset`. `⊂` is
`LT.lt` the same way. The parser reads `⊆` as `HasSubset.Subset` only, so a
pattern copied from a `Set` goal misses exactly the lemmas it was copied from.
And a `⊆` nested in a pattern becomes `--uses HasSubset.Subset`, which rules
those lemmas out even where the conclusion is something else.

Seen with dt 0.55.0, 2026-09-21.

Fixed in 0.56.0. A conclusion written `⊆` is matched under `HasSubset.Subset`
and under `LE.le`, and one written `⊂` under `HasSSubset.SSubset` and `LT.lt`
-- in the SQL filter, in the domain's shape match and in the ranking alike, so
the probes that diagnose a miss ask what the search asked. One way only: `≤`
still asks for an order. `⊂` is notation to the parser now; it was read as
nothing. A `⊆` or `⊂` anywhere but the head, a hypothesis included, is no
`--uses` condition, since it could name only one of its two constants.

    $ dt find "f '' (s ∩ t) ⊆ _"          -> Set.image_inter_subset, ...
    $ dt find "s ⊆ t → f '' s ⊆ f '' t"    -> Set.image_mono, ...
    $ dt find "_ ⊂ insert _ _"             -> Set.ssubset_insert, ...

## Patterns reject the set notations `⁻¹'` and `×ˢ`

Found 2026-09-21, dt 0.54.0, on a Lean project beside Mathlib. I wanted the
lemma rewriting a product with `univ` into a preimage under `Prod.fst`:

    $ dt find "Prod.fst ⁻¹' _ = _ ×ˢ Set.univ"
    No match: `'`, `×` in the pattern read as nothing here; searching without
    them would answer a wider question — write the constant it stands for
    instead, or drop that part of the pattern and give it as --uses

Spelling the constants out did not help either:

    $ dt find "Set.preimage Prod.fst _ = Set.prod _ Set.univ"
    No match: nothing has that shape; each of `Set.preimage`, `Set.prod`
    matches without the others

The lemma exists: `Set.prod_univ : s ×ˢ Set.univ = Prod.fst ⁻¹' s`, which
`dt find --name prod_univ --in Mathlib.Data.Set` found at once. Two gaps:
`⁻¹'` and `×ˢ` are ordinary Mathlib notation (`Set.preimage`, `SProd.sprod`)
and should elaborate in a pattern; and the spelled-out form missed because
`×ˢ` is `SProd.sprod`, not `Set.prod`. The error could name the constant a
notation stands for, or at least accept `SProd.sprod`. The right output for
the first command is `Set.prod_univ` (the equation up to symmetry).

Fixed in 0.55.0. `⁻¹'`, `''` and `×ˢ` are notation to the pattern parser, for
`Set.preimage`, `Set.image` and `SProd.sprod`, at Mathlib's own strengths (80,
80, 82, all to the right). The lexer had cut them into a postfix `⁻¹` and a
name `'`, an identifier `''`, and a `×` beside a one-letter variable `ˢ`.

And an `=`, `↔` or `≠` pattern that matches nothing is searched again with its
two sides traded, the rows marked on stderr as turned, since a lemma stating
the other side first is the same lemma with one `.symm`. So the first command
now answers `Set.prod_univ`. An order is not turned; its miss still says the
other way round matches.

The second command is still `no match`, and correctly: `Set.prod` is a
constant of its own and `Set.prod_univ` does not mention it. Written with
`SProd.sprod` it answers. Telling a reader that the definition they named is
what a notation class unfolds to would need the instances, which the index
does not keep.

Found on the way, not fixed here: `⊆` on sets is `HasSubset.Subset` to the
parser and `LE.le` in the index, because Mathlib's `Set` subset is its order.
`f '' (s ∩ t) ≤ _` finds `Set.image_inter_subset`; `f '' (s ∩ t) ⊆ _` names
`LE.le` among the relations those arguments go together under.

## A `--in` miss blames `--in`, when the module it names is populated and it is `--name` that matches nothing

Found 2026-09-19, dt 0.53.0, on a Lean project of my own beside Mathlib,
Batteries and core. I was looking for a declaration about addresses in my own
`Transformer.ALM`:

    $ dt find --name addr --in Transformer.ALM
    no match: drop --in — without it the rest matches in Std.Net.Addr (90),
    Mathlib.Algebra.Regular.SMul (26), Mathlib.Algebra.Regular.Basic (22),
    Mathlib.Algebra.Order.Group.Synonym (18), and 105 more

The advice is literally true — dropping `--in` does produce matches — but it
points at the one condition that was right. `Transformer.ALM` exists, is
indexed, and is exactly the module I meant:

    $ dt find --in Transformer.ALM --limit 5
    Transformer.ALM.NNIndex  structure  Transformer.ALM.LookupIndex
    ...
    5 shown, more match; refine or --limit

So the fact I needed was "that module has declarations, none of them named
`addr`" — i.e. my *name* guess was wrong and my *module* guess was right. The
message told me the opposite, and the 105 unrelated modules it listed are
noise: I had already said I did not want them.

The blame heuristic seems to pick the condition whose removal yields the most
rows. That maximises rows, not information. A condition the user narrowed
deliberately (`--in`, `--source`) is a statement of intent; a condition that is
a guess (`--name`, `--text`) is the likelier culprit, and when the narrowing
condition on its own has a non-empty result that is the fact worth reporting.

What the right output would be:

    no match: Transformer.ALM has 2578 declarations, none named `addr`
      (drop --in and `addr` matches in Std.Net.Addr (90), and 108 more modules)

That is, when a scope condition alone is non-empty, name it and its size first
and say which of the remaining conditions emptied it; keep the current message
for the case where the scope itself is the empty one — which is also the case
where "drop --in" is genuinely the right advice, and where it would be worth
distinguishing a module prefix that is indexed but unmatched from one that is
not in the index at all.

Fixed in 0.54.0. `--in` and `--source` are now read as the scope of a search
and not as conditions of it. When the scope holds anything, the answer leads
with its size and with which of the remaining conditions found nothing inside
it:

    $ dt find --name addr --in Transformer.ALM
    no match: Transformer.ALM has 877 declarations, none matching --name addr
      (drop --in and the rest matches in Std.Net.Addr (90), ..., and 105 more module(s))

The modules the rest of the query matches in are kept, indented and second, for
the reader whose module guess was wrong after all. A scope that holds nothing
still reads `--in X matches nothing on its own`, which is the case where the
scope is the condition to correct. The count is a `count(*)` over the same
filter the search uses, so it costs one row, not a page; with one condition
beside the scope no probe runs at all, because the search that just missed is
that probe. A miss on the probe project went from 0.96 s to 1.15 s.

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

Fixed 2026-09-15 in dt 0.13.0, as a diagnosis rather than as a rule about
`Mathlib.olean`:

    dt: lake env lean failed for source `nope` (exit 1); `Nope.olean` was built
    by Lean 4.33.1 and lean-toolchain says 4.34.0 -- run `lake build` first

An `.olean` carries the Lean that wrote it in its header -- the magic, two
bytes of format version, then the version string -- and `lean-toolchain` says
which Lean was meant to write it, so the diagnosis is two files and a
comparison, with no Lean and no lake in it.  The repair names the module when
the `.olean` belongs to a package (`lake build Mathlib`) and does not when it
is the project's own build (`lake build`), which is the only thing that differs
between the two cases.  The script path is what is printed when there is no
diagnosis, which is where it belongs: for a failure that is not a stale build
-- a syntax error in the script, an import the root does not pull in -- the
script is exactly what to look at.

Nothing is claimed unless both files can be read and the toolchain is a
released version.  A nightly names no version an `.olean` could be compared
against, and a confident wrong diagnosis is worse than an exit code on its own.

The header was calibrated against real files: `Mathlib.olean` from a v4.34.0
build reads `4.34.0` at offset 7, and the reproduction is an `.olean` edited to
carry v4.33.1's version string *and* git hash -- both, because Lean accepts a
header whose version string alone was changed.  The git hash is what it
compares; the version string is what a reader can act on.

What is not done is the paragraph above this one.  The dump still imports
`Mathlib` and still needs `Mathlib.olean`.  Splicing the 8 531 import lines of
`Mathlib.lean` in its place would save three minutes once per toolchain bump,
and would cost a text parse of an umbrella file that is no longer a list of
`import` lines -- Mathlib v4.34.0 opens with `module` and every line reads
`public import` -- plus a rule for umbrella files that declare something of
their own.  A new failure surface on the one path that cannot be tested without
a Lean on the machine, for three minutes a month, is the wrong trade; the
sentence naming the repair is what the session that reported this actually
needed.

## Single-letter pattern variables are read as constants

`dt find 'a ≤ b → b⁻¹ ≤ a⁻¹'` (looking for `inv_anti₀`) answers

    no match: `a` in the pattern, `Arrow` in the pattern, --uses a, --uses b
    match nothing on their own

so `a` and `b` were elaborated as names to look up rather than as pattern
variables, and the arrow shape was searched for as a constant `Arrow`.  The
same query with `_ ≤ _ → _⁻¹ ≤ _⁻¹` is what one has to write, but a bare
lowercase identifier that resolves to nothing is far more likely to be a
metavariable the user spelled the Lean way (`∀ {a b : α}, a ≤ b → ...` is how
the statement is printed by `dt show` itself) than a declaration named `a`.
Either treat an unresolvable single-letter identifier as a wildcard, or say so
in the failure message -- the current one names four conditions and does not
hint that the fix is `_`.

Hit twice in one session: the fallback both times was `dt find --name`, i.e.
guessing the name, which is the thing `dt find` exists to avoid.

Fixed in 0.15.0.  A binder is one letter and whatever decorations the printer
put on it -- `a`, `x'`, `f₁`, `α` -- and nothing global is spelled that way, so
that is the rule: a token of that shape is a wildcard, wherever it appears.  It
never reaches `--uses`, and a side of a relation whose head is one is `_`.  The
test is syntactic rather than a lookup in the index, because a lookup would make
the same pattern mean different things in two projects, and the project where
something really is called `a` is the project where that is a typo.

`dt find -v` now names what it read as a wildcard, which is where a rule this
quiet belongs: the pattern is echoed as `conclusion LE.le, 2 argument(s),
operator `≤`, `a`, `b` as `_``.

## Implication patterns do not match hypothesis-shaped lemmas

`dt find 'HasFDerivAt _ _ _ → HasFDerivAt _ _ _ → HasFDerivAt _ _ _'
--text inner` answers "no match: every condition matches on its own; drop
one", but `HasFDerivAt.inner` exists and has exactly that shape:

    theorem HasFDerivAt.inner (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
        HasFDerivAt (fun t => ⟪f t, g t⟫) ((fderivInnerCLM 𝕜 (f x, g x)).comp <| f'.prod g') x

Hypotheses are binders, not arrows, in the elaborated term, so a `→` pattern
misses every lemma stated with named hypotheses -- which is most of Mathlib.
A pattern whose top level is `→` should match a pi type over the same
argument types.

Fixed in 0.16.0.  `→` is split off before anything else and never becomes a
head symbol: what follows the last arrow is the conclusion and is parsed as
the whole pattern used to be, and each hypothesis contributes its head symbol
and its constants as `--uses`.  That is what a hypothesis can honestly say --
it is in the type, so it is in `consts` -- and the shape is the conclusion's
alone, which is how the index has always been keyed.  `Arrow` is gone from the
notation table; nothing declares it, and no elaborated conclusion can be one.

The same pattern needed two smaller things to work.  `⁻¹` is one token now
(Rust calls `¹` numeric, so `b⁻¹` tokenized as `b` and an identifier `¹`) and
maps to `Inv.inv`, and notation carries how loosely it binds, so the head
symbol of a side is its loosest operator rather than its first: `a⁻¹ + b⁻¹` is
an addition.  `->` reads as `→`, which a keyboard has.

Verified against the real index:

    $ dt find 'HasFDerivAt _ _ _ → HasFDerivAt _ _ _ → HasFDerivAt _ _ _' --text inner
    HasFDerivAt.inner  theorem  Mathlib.Analysis.InnerProductSpace.Calculus
    1 result(s)

    $ dt find 'a ≤ b → b⁻¹ ≤ a⁻¹'
    ENNReal.inv_le_inv'  ...  Filter.inv_le_inv  ...  inv_le_inv'  ...

## "`project` moved since it was indexed" on every query

Every `dt` call in this session, in the directory the project was indexed
from (`/home/misha/lean_projects/transformer`, unmoved), prints

    dt: `project` moved since it was indexed; this answer may be out of date
    -- re-run `dt refresh project`

It shows up attached to failed searches, where it reads as the explanation for
the failure and is not.  Whatever the move check compares (a symlinked or
`/proc`-resolved path?), it is reporting a move that did not happen.

Fixed in 0.17.0, though not where it was looked for.  The check was right and
the word was wrong.  Nothing compares paths: a `local` source's revision is a
fingerprint of `.lake/build/lib`, and in that project it really had changed --
`b57d6d7` when the dump was taken, `04e1042` at the time of the report, which
`dt status` had been showing all along as `b57d6d7 (now 04e1042, stale)`.  The
project was being rebuilt between searches, which during development it always
is.  But "moved since it was indexed" reads as a claim about a directory, the
directory had not moved, and the only conclusion left was that the check was
broken.

So the line says which value differs, and says it in the words that fit the
source:

    dt: `project` was rebuilt since it was indexed; rows may be missing
        — `dt refresh project`
    dt: `mathlib` is at 4f8b12c, the index at 5ed2965; rows may be missing
        — `dt refresh mathlib`

A revision pair is something a reader can check; "moved" is something they can
only argue with.  The project gets the fact rather than the pair because its
revision is a build fingerprint -- two of those side by side say nothing, and
nobody pastes one into `git show`.  A toolchain keeps its whole name for the
same reason: `leanprover/lean4:v4.34.0` cut to seven characters is `leanpro`.

What is left standing is the volume.  A project that is being compiled while it
is being searched is behind its own build most of the time, and the warning is
correct every time it fires.  Narrowing it -- to the sources a failed search
could plausibly have drawn on, rather than all of them -- is a separate change
and needs the query's own conditions to say which those are.

## `dt refresh` exits 0 after failing to rebuild a source

Reported 2026-09-15, from the transformer project, dt 0.17.x.

The project did not compile at the moment `dt refresh` ran (a file mid-edit).
The dump script could not load one module, and `dt refresh` said so -- and then
exited `0`:

    $ dt refresh; echo "[exited with code $?]"
    .../dump_project.lean:20:0: error: object file '.../Section8_General.olean'
      of module Transformer.Perspective.Section8_General does not exist
    dt: lake env lean failed for source `project` (exit 1); the script is at
        .../.discrtree/jsonl/scripts/dump_project.lean
    [exited with code 0]

The message is clear and names the script, so a human reading the terminal is
fine.  A caller is not: anything that runs `dt refresh` before a batch of
queries -- a shell `&&` chain, a Makefile, a pre-commit hook, an agent -- sees
success and goes on to search a stale index, which is the exact state the
refresh was meant to leave behind.

Expected: a non-zero exit when no source was refreshed.  A partial refresh
(mathlib fresh, project failed) is the interesting case: either non-zero with
the per-source status kept in the output, or a documented convention, but not
`0`.

Not reproduced, and the convention written down instead, in 0.19.0.

Every version that has a `refresh` at all -- it arrived in 0.10.0 -- propagates
the failure with `?` and `main` turns any `Err` into `dt: <reason>` and exit 1.
Reading the whole path again (`refresh`, `read_each`, `dispatch`, `run`, `main`,
`dump`, `LakeElaborator::dump`) found nothing that swallows one.  Then the
report's own failure was staged on a toy project by deleting a module's
`.olean`, which is the error it quotes:

    $ dt refresh toy; echo "[exit $?]"
    .../dump_toy.lean:20:0: error: object file '.../Toy/Basic.olean' of module
      Toy.Basic does not exist
    dt: lake env lean failed for source `toy` (exit 1); the script is at
        .../dump_toy.lean
    [exit 1]

    $ dt refresh; echo "[exit $?]"          # two stale sources, both broken
    dt: `nope`: lake env lean failed for source `nope` (exit 1); ...
    dt: `toy`: lake env lean failed for source `toy` (exit 1); ...
    dt: 2 of 2 sources could not be read and were left as they were: nope, toy
    [exit 1]

A missing name, one stale source, two stale sources, a partial failure: exit 1
every time.  So the `0` came from somewhere the binary cannot see -- a pipeline
whose `$?` belonged to the last stage, a shell function, an older build on the
`PATH` -- and there is nothing here to fix.

What there was, was nothing holding the convention in place: no test covered
the single-target failure, and `--help` said what a refresh does but not what it
exits.  The decision now lives in one function, `outcome(targets, failed)`, with
the three cases named as tests -- one source fails with its own reason, a
partial refresh is still a failure, everything read is the only success -- and
`dt refresh --help` states it for the caller that reads exit codes rather than
terminals.  A report of the same thing against a version that has these tests
would be worth chasing; this one is closed as unreproducible.

## `--kind instance` matches nothing in an elaborated source

dt 0.17.x, index built from `Mathlib` (lake), `core`, `batteries` and a local
`project`, plus one text-scanned source.

`dt find --help` lists `instance` among the kinds:

    --kind <KIND>
        theorem, def, structure, inductive, axiom, instance, ctor

and it does select rows -- but only from the text-scanned source:

    $ dt find --kind instance | head -2
    AlgebraicGeometry.ThetaLevel.Heis.instMul  [text]  instance  Definitions...
    AlgebraicGeometry.ThetaLevel.Heis.instOne  [text]  instance  Definitions...

In every elaborated source an instance is recorded as `def`:

    $ dt find --kind instance --in Mathlib.Topology
    no match: every condition matches on its own; drop one

    $ dt find --name instMeasurableSpace --in Mathlib | head -1
    Int.instMeasurableSpace  def  Mathlib.MeasureTheory.MeasurableSpace.Instances

So the one filter a user reaches for when asking "does this type have an
instance here" excludes every instance in the sources they actually search,
and says so in the vocabulary of an empty result rather than of a missing
feature. What went wrong on this end: I asked whether the sphere's
`MeasurableSingletonClass` instance existed, read `no match` as "it does not",
and went to write it by hand; Lean found it by `infer_instance` on the first
try.

Either would fix it: record `instance` as its own kind when dumping from Lean
(`ConstantInfo` carries the attribute), or -- if that is a deliberate
simplification -- have `--kind instance` say that the kind is not distinguished
in elaborated sources, the way an unknown `--source` is an error rather than an
empty result.

Fixed in 0.20.0, in the dump, with a message for the indexes written before it.

Lean has no `instance` constant.  An instance is a `defnInfo` carrying an
attribute, and `declKind` read the constructor alone, so every instance in
every elaborated source came out as `def` -- correct about the constant and
useless for the question being asked.  The attribute is one lookup away
(`isInstanceCore env ci.name`, the same table `infer_instance` searches), and
it now wins over `def`, which is how the text scanner has always spelled it:

    $ dt find --kind instance --source toy
    instInhabitedBox  instance  Toy.Basic
      Inhabited Toy.Box
    $ dt find --name plain
    Toy.plain  def  Toy.Basic

The cost of that is `--kind def` no longer matching an instance.  That is the
same trade the text scanner made, and it is the one that answers the question
people actually ask: "is there an instance of this class for this type" is a
search, "is there a def that happens to be an instance" is not.

The rest of the entry is the indexes that already exist.  A dump written before
this change records instances as `def` and nothing on disk has moved, so the
index is not stale by any measure `dt status` has, and `dt refresh` with no
name will say there is nothing to do.  The empty result says it instead:

    $ dt find --kind instance --in Toy.Basic
    no match: no elaborated row carries the kind `instance`; a dump older than
    dt 0.20.0 records every instance as `def` — re-read the source to get them:
    `dt refresh <source>`

which fires only when the index holds no elaborated instance at all, and stops
firing the moment one source has been read again.  Reaching it needed a probe
before the per-condition ones, because `--kind instance` does match on its own
-- on the text rows -- and the diagnosis was therefore "every condition matches
on its own; drop one", the one repair that could not have helped.

Existing indexes need `dt refresh <source>` per elaborated source to pick the
kind up; for Mathlib that is a full dump again, and there is no shortcut, the
kind is written by the dumper and nowhere else.

## A pattern head that the row prints as `inner` has to be spelled `Inner.inner`

Looking for the coordinate formula of the inner product on `EuclideanSpace`,
every shape query with `inner` as the head fails, and one of them fails with a
message that says the head is the problem:

    $ dt find 'inner _ _ = ∑ _, _'
    no match: `inner` in the pattern matches nothing on its own
    $ dt find 'inner _ _ _'
    no match
    $ dt find '⟪_, _⟫_ℝ = _'
    no match: `_ℝ` in the pattern matches nothing on its own

The rows are there, and they print the head as `inner`:

    $ dt find --name inner_apply --in Mathlib.Analysis
    Real.inner_apply  theorem  Mathlib.Analysis.InnerProductSpace.Basic
      ∀ (x y : ℝ), inner ℝ x y = x * y

What matches is the qualified name, which appears nowhere in the output:

    $ dt find 'Inner.inner _ _ = _'
    Real.inner_apply  theorem  Mathlib.Analysis.InnerProductSpace.Basic
      ∀ (x y : ℝ), inner ℝ x y = x * y

`inner` is an `export Inner (inner)`, so the pretty-printer drops the namespace
and the pattern parser does not put it back.  The same will hold for every
other exported class field one might reach for as a head (`compl`, `toDual`,
`smul`...), and the message is confidently wrong about it: `inner` matches
nothing on its own *as written*, but the constant it abbreviates is the head of
hundreds of indexed rows.

Two repairs, either of which would have saved the guessing:

- resolve an unqualified pattern head through the same `export`/`open`
  aliases Lean uses, so `inner _ _ = _` finds `Inner.inner`;
- failing that, have the message name the candidates it knows about --
  "`inner` matches nothing on its own; did you mean `Inner.inner`?" -- since
  the index already holds the qualified constant and the unqualified suffix.

Note also that `inner _ _ _` -- the arity the row actually prints, `𝕜` being
explicit since the 2025 signature change -- returns a bare `no match` while
`inner _ _ = _` returns the diagnosed one, so the more accurate query gets the
less informative answer.

Fixed in 0.21.0, by the first repair: an unqualified head is resolved through
the index itself.  There is no alias table to consult -- the dump records
constants, not the `export` statements that name them -- but the index knows
something better than the aliases do, which is how often each candidate is
actually the head of a row.  A pattern word with no dot in it is looked up
among the head symbols whose last component is that word, and the commonest
wins: `inner` finds 78 constants ending in `.inner`, `Inner.inner` heads 376
rows and the runner-up heads 8.  Ties go to the shorter name, then
alphabetically, so the answer does not depend on the order the rows arrived in.

The lookup runs only when the query as written found nothing, and the rewrite
is announced, because a search that silently answered a different question than
the one asked would be worse than an empty result:

    $ dt find 'inner _ _ = ∑ _, _'
    dt: `inner` read as `Inner.inner`
    sum_inner  theorem  Mathlib.Analysis.InnerProductSpace.Basic
    ...
    PiLp.inner_apply  theorem  Mathlib.Analysis.InnerProductSpace.PiL2

The line goes to stderr, so a pipe still carries only results.  A word that is
itself a head symbol is left alone -- `Eq` is spelled `Eq` in the index and is
also the last component of several other constants -- and a word written twice
in one pattern is resolved once and reported once.

When the rewrite finds nothing either, the message says what the index calls
the word instead of leaving the user to guess, which is the entry's second
repair and costs nothing once the first is in place:

    $ dt find 'inner _ _ _'
    no match: `inner` is `Inner.inner` in the index — Lean prints an exported
    name without its namespace — and that matches nothing either; also
    `Std.DTreeMap.Internal.Impl.inner`, `Std.DTreeMap.Internal.Cell.inner`

so the more accurate query now gets the more informative answer, which is the
last paragraph of the entry.

Ranking is read from `decl`, whose `concl` is indexed, not from the `uses`
side table: on the real 1.2 GB index a `decl` scan is 0.14-0.23 s against 3.8 s
cold for `uses`, and both count the same thing.  The rule itself lives in
`domain::decl::commonest_called`, so the in-memory stores and the SQL count
agree by construction rather than by inspection.

Not fixed here: `⟪_, _⟫_ℝ`, the notation spelling from the third query above.
That is the parser's problem, not the resolver's -- notation is not a name, and
the index holds no notation -- so it got its own follow-up below.

### Follow-up: the notation spelling of the same query

    $ dt find '⟪_, _⟫_ℝ = _'
    no match: `_ℝ` in the pattern matches nothing on its own

Fixed in 0.22.0, in the tokenizer and the notation table, which is where every
other operator a user types is already handled.  Two things were wrong and only
the second one showed:

- `⟪` was not in the table, so the side it heads contributed no head symbol;
- `⟫_ℝ` tokenized as the closing bracket and an *identifier* `_ℝ`, which then
  became a `--uses` condition on a constant no project declares.  That is the
  condition the message named, and it is the one thing in the pattern the user
  could not have written differently.

The type a bracket notation is ascribed with belongs to the bracket, the way
`¹` belongs to `⁻` -- which the tokenizer already knew, for the same reason --
so `⟫` now absorbs a following `_ℝ`, `_𝕜` or `_ℂ`, and `⟪` maps to
`Inner.inner` at the precedence of the other bracket notations:

    $ dt find '⟪_, _⟫_ℝ = _'
    Real.inner_apply  theorem  Mathlib.Analysis.InnerProductSpace.Basic
      ∀ (x y : ℝ), inner ℝ x y = x * y
    Quaternion.inner_def  theorem  Mathlib.Analysis.Quaternion
      ∀ (a b : Quaternion ℝ), inner ℝ a b = (a * star b).re

Whichever field is named, and naming none, read the same: the notation says
which constant, never which instance.

A pattern that is *nothing* but notation used to fall through to a free-text
search, because the fallback looked for an identifier and notation has none.
`⟪x, y⟫_ℝ` and `‖x‖` now yield their head symbol with no arguments -- notation
hides the implicit arguments, so the head is all that can honestly be claimed,
and a head alone is still a shape search rather than a text one.

`⟪_, _⟫_ℝ` on its own is still `no match`, and correctly: nothing in Mathlib
*concludes* an inner product, it concludes an equation between two of them.
`Inner.inner _ _` spelled out gets the same answer, so the notation is no
longer the odd one out, which is all this entry asked for.

## A shape query over a notation-only conclusion drifts to unrelated rows

`|a + b| ≤ |a| + |b|` is `abs_add_le` in
`Mathlib.Algebra.Order.Group.Unbundled.Abs`.  Asked by shape:

    $ dt find '|_ + _| ≤ |_| + |_|'
    Int.add_le_add_right  theorem  Init.Data.Int.Order
      ∀ {a b : Int}, a ≤ b → ∀ (c : Int), a + c ≤ b + c
    Nat.add_le_add_left   theorem  Init.Data.Nat.Basic
    Nat.add_le_add_right  theorem  Init.Data.Nat.Basic
    Int.add_le_add_left   theorem  Init.Data.Int.Order
    Int.add_le_add        theorem  Init.Data.Int.Order

Five rows, none of them with an absolute value anywhere in the statement.
The `|_|` on both sides was dropped and what was matched is `_ + _ ≤ _ + _`.
A pattern whose distinguishing feature is silently discarded is worse than
`no match`: `no match` says which condition to blame, these rows say nothing.

Same shape as the earlier `_ = -_ ↔ _ = 0` entry: when part of a pattern
cannot be resolved, the answer should narrow to `no match` and name the part,
not widen to whatever remains.

`dt find --name abs_add --kind theorem` does find `abs_add_le`, so the row is
indexed and elaborated; only the shape query misses it.

Fixed in 0.23.0.  `|` was not in the notation table, but adding it would not
have fixed anything: `‖_ + _‖ ≤ _` had the identical defect with a bracket that
*was* in the table, and returned rows whose left side was any addition at all.

The head of a side was chosen as the loosest notation anywhere on it, which is
right for infix -- `a⁻¹ + b⁻¹` is an addition -- and wrong for a bracket, which
is not an operator *on* the side but the side itself.  Brackets are now their
own kind of notation with no binding strength at all:

    (  )    grouping, applies nothing
    ‖  ‖    Norm.norm
    |  |    abs
    ⟪  ⟫    Inner.inner

A bracket that encloses the whole of a side is that side's head whatever is
inside it; otherwise the loosest infix *at depth zero* wins, so `|_| + |_|` is
still an addition.  Parentheses are tokenized rather than discarded, for the
same reason -- they group, and the head is what they group -- and the relation
a pattern splits on is now the first one at depth zero.

    $ dt find '|_ + _| ≤ |_| + |_|'
    abs_add_le  theorem  Mathlib.Algebra.Order.Group.Unbundled.Abs
      ∀ ... (a b : α), |a + b| ≤ |a| + |b|
    abs_add'    theorem  Mathlib.Algebra.Order.Group.Abs
    abs_sub     theorem  Mathlib.Algebra.Order.Group.Abs

The second half of the entry -- narrow rather than widen -- is now a rule
rather than a table.  A symbol that is neither notation, nor a bracket, nor
punctuation used to be read as nothing, which silently loosened the pattern.
It is reported instead:

    $ dt find '_ ∩ _ ⊆ _'
    no match: `∩` in the pattern reads as nothing here; searching without it
    would answer a wider question — write the constant it stands for instead,
    or drop that part of the pattern and give it as --uses

This is an empty result rather than an error: the pattern is not malformed, it
is understood by Lean and not by `dt`, and `no match` naming the part is the
answer that can be acted on.  A pattern that falls through to a text search
reports nothing, because nothing was dropped there -- the whole of it is what
is searched for.

Punctuation had to be enumerated for that rule to be usable, and the first
draft was wrong in the direction that matters: it refused `a + 1 ≤ b`, because
a numeral is not an identifier.  Literals now read as what the index actually
stores for them -- `Nat.zero_lt_one` is `LT.lt` over two `OfNat.ofNat`s -- so
`0 < 1` is a shape and not a complaint, and `--uses 1` is never searched for.

Two things this does not do, both older than the entry:

- `‖_ + _‖` still keys on `Norm.norm` alone.  The `+` is one level further
  down than the index stores, which is phase 5 and not a parsing question.
- a statement pasted whole, `∀ {a b : Int}, a + 1 ≤ b ↔ a < b`, still reads
  its binders as part of the left side.  The shape in the index is read with
  every binder stripped and the parser does not strip them; that wants its own
  entry.

## An exactly-matching name is not ranked above its own prefixes

`--name` is a substring filter, and within the matches nothing prefers the
row whose name *is* the query. Asking for a declaration by its full name
therefore buries it:

    $ dt find --name "Real.sin_sq"
    Real.sin_sq_le_one       theorem  Mathlib.Analysis.Complex.Trigonometric
    Real.sin_sq_le_sq        theorem  ...Trigonometric.Bounds
    Real.sin_sq_lt_sq        theorem  ...Trigonometric.Bounds
    Real.sin_sq              theorem  Mathlib.Analysis.Complex.Trigonometric
    Real.sin_sq_add_cos_sq   theorem  Mathlib.Analysis.Complex.Trigonometric
    Real.sin_sq_eq_half_sub  theorem  Mathlib.Analysis.Complex.Trigonometric

`Real.sin_sq` is there, fourth, under three of its own suffixes. With the
default limit of 10 a name with more than ten descendants (`Finset.sum`,
`Real.exp`, `List.map`) drops off the page entirely, and the caller reads
`6 result(s)` as "the exact name is not indexed" rather than "look further
down".

`dt show Real.sin_sq` answers correctly, so this is only about ordering:
an exact name match should sort first, and a prefix match ahead of an
interior one. The filter itself is right — the ranking is what is missing.

Fixed in 0.24.0.  Ranking, as the entry says, and in two places for one rule.

`query::rank` scores how much of the row's name the query accounted for, ahead
of everything else it scores: a name given in full is worth more than the shape
agreement below it, because a caller who writes the whole name has said which
row they want and nothing else in the query says it more precisely.

    the name is the query              8
    the query is the name, unqualified 6   `sin_sq` for `Real.sin_sq`
    the name begins with the query     2
    the query is somewhere inside it   0

Case-insensitively, because the filter is.  The old tie-break -- shortest type
first -- is what put `Real.sin_sq_le_one` on top, and still decides between
rows that score the same.

    $ dt find --name Real.sin_sq
    Real.sin_sq          theorem  Mathlib.Analysis.Complex.Trigonometric
      ∀ (x : ℝ), Real.sin x ^ 2 = 1 - Real.cos x ^ 2
    Real.sin_sq_le_one   theorem  Mathlib.Analysis.Complex.Trigonometric
    ...
    $ dt find --name sin_sq
    Real.sin_sq          theorem  Mathlib.Analysis.Complex.Trigonometric
    Complex.sin_sq       theorem  Mathlib.Analysis.Complex.Trigonometric

The second place is the one the entry could not see.  Ranking happens in the
domain over a window of rows SQLite is asked for -- 200 for a name query -- and
for a name that is also a namespace the window is filled before the row itself
is reached: `dt find --name Real.exp` returned `EReal.exp_bot` first out of
thousands, and `Real.exp` was not below it, it was absent.  The SQL now orders
by the same three tests before the cap, so the window is filled with the rows
the domain would choose.  Sorting is what `LIKE '%x%'` costs anyway: on the
1.2 GB index `--name Real.exp` is 0.21 s, unchanged, and the worst case that
exists -- `--name e`, 463 306 matching rows -- is 0.37 s.

Neither half works without the other, and each is testable on its own: the
ranking against a handful of rows in the domain, the window against 301 rows
in SQLite with the answer written last.

## A dt version bump leaves the old index silently incomplete

After upgrading 0.22.0 → 0.24.0, `dt status` reported only `project` as behind:
`mathlib` was "1h ago, revision 5ed2965", no warning. But that index had been
dumped by 0.22.0, and lookups against it came back empty:

    $ dt show ContinuousLinearMap.adjoint
    dt: ContinuousLinearMap.adjoint is not in the index; try `dt find --name adjoint`
    $ dt find --name adjoint --in Mathlib.Analysis.InnerProductSpace --kind def
    no match: every condition matches on its own; drop one

`dt refresh mathlib` — which `dt status` said was unnecessary, and which
`dt refresh` with no argument therefore skips — fixed both: the same two
queries now answer with `Mathlib.Analysis.InnerProductSpace.Adjoint`.

Staleness is tracked against the *source* revision only, never against the
version of `dt` that wrote the rows. So the failure mode is an index that
looks current and answers `no match` for declarations that are in it. The
answer is wrong rather than late, and `--kind def` makes it look like a
deliberately narrowed query returning nothing.

Suggestion: stamp the writer's version into the index, and have `dt status`
mark every source written by an older `dt` as stale, so plain `dt refresh`
picks them up.

Fixed in 0.25.0. The suggestion, with one number added to it: the index now
records both the `dt` that wrote each source and the *row format* it wrote it
in, and staleness is decided by the second rather than the first. They are not
the same test. Most versions of this tool change what it does with a row —
ranking, parsing, what it prints — and leave every stored row exactly as it
was; marking Mathlib stale on those would cost an hour of Lean to rediscover
that nothing had changed, and a warning that fires on every upgrade is a
warning that gets refreshed past without reading. `ROW_FORMAT` is a single
constant bumped by hand when a dump would now produce different rows, and the
comment on it says which way to err.

A row format nobody recorded reads as older than the current one. That is the
opposite of the rule revisions follow — unknown is not stale there, because a
revision nobody could read is no evidence a source moved — and the asymmetry is
the point: a missing row format is not a gap in what could be read, it is a
positive fact about who wrote it. Only a `dt` from before this existed leaves
it empty. So an index like the one in the report says so about itself the first
time the new build opens it.

Which it does open. A schema bump refuses the file and asks for
`dt index --rebuild`, and that is right when the columns would be misread —
here they would not be: every old column still means what it meant, and the two
new ones are nullable and empty, which is exactly the fact worth having. So
schema 2 is migrated in place by two `ALTER TABLE`s. Verified on a copy of the
1.2 GB index from the report: `PRAGMA user_version` 2 → 3, all 494 731 rows
kept, `dt status` then naming every source as behind.

The repair is split from the diagnosis, because the two kinds of staleness do
not cost the same. A source that has *moved* has to be read again — dumped,
fetched — before it can be loaded. A source that holds old rows has not moved:
the dump on disk is the right dump, and re-reading it out of Lean would spend
an hour producing bytes that are already there. So `Stale` now carries why, and
`dt refresh` re-reads only what moved and re-loads the rest. On that same copy,
with the dumps it already had, the whole re-load was 83 seconds.

`dt status` says it in the line that was silent:

    behind: project, mathlib, flt, batteries, core — indexed by an older dt — re-run `dt refresh`

and a search that touched such a source says it per source on stderr, with both
versions, the way the revision warning says both revisions. An upgrade puts
every source behind at once and for one reason, so the shared reason is said
once; a mixed list spells it out per name, because then it is more than one
fact. `dt index` no longer skips such a source either: its stamp answers "is
the input the same input", which was never the question being asked.

---

## `dt show` can point at a docstring instead of the declaration

    $ dt show MeasureTheory.integral
    import Mathlib.MeasureTheory.Integral.Bochner.Basic

    MeasureTheory.integral
      def  Mathlib.MeasureTheory.Integral.Bochner.Basic:157-161
      those lines declare nothing: `/-- The Bochner integral -/`

The range is the declaration's *documentation*, not the declaration, so the
one line `show` exists to print — the statement — is replaced by a complaint
about the source it just read. The row is otherwise right: the name resolves,
the import line is correct, the kind is correct.

Whatever computes the line range is taking the start of the declaration's
syntax including its doc comment and then a length that stops inside it. A
declaration with a docstring is the common case in Mathlib, so this is not an
edge: it is one whole class of `show` answers that comes back empty. Either
extend the range past the doc comment, or, when the extracted text parses as
nothing but a comment, fall back to the elaborated type that the index already
holds — an answer from the index beats a wrong answer from the file.

Fixed in 0.26.0. The range is right: lines 157-161 are the docstring *and* the
declaration, and `dt show` had already printed them if it had recognised what
followed. What it did not recognise was the command. `irreducible_def` is not
`theorem`, `lemma`, `def` or any of the eight other words the text reader knows,
and that list cannot be completed — Mathlib defines commands of its own, and a
library may define one tomorrow.

So the question changed. Asking "do these lines declare something" needs the
list of declaration commands; asking "do these lines declare *this name*" does
not. A word at column zero followed by the name Lean printed is that name's
header, whatever the word is, and the only list still needed is the closed one:
the commands that take a name and do not declare it (`namespace`, `open`, `end`,
`import`, and nine more). A library can add a way to declare something. It
cannot add a way to open a namespace.

Three things fell out of reading real ranges:

- the file writes whatever suffix of the name the surrounding namespaces leave,
  and that suffix is more than the last component — `namespace Matroid` makes
  `Matroid.IsRkFinite.diff_singleton_iff` into `IsRkFinite.diff_singleton_iff`.
  `_root_.` is the opposite instruction and what follows it is the whole name;
- `alias ⟨_, biUnion⟩ := h` binds two names, and either may be the one asked
  about;
- `meta def` and `public theorem` are declarations with a modifier, not
  commands named `meta` and `public`.

Comments are now dropped by the line rather than by nesting depth, so the line
that *opens* a docstring is no longer read as syntax, and the head printed when
a range really does declare nothing is its first line of code. That head is the
useful half of the complaint: `@[inherit_doc] notation "‖" e "‖₊" => nnnorm e`
says what produced the row, where `/-- The nnnorm -/` said only that the
declaration has documentation.

Measured over 4000 consecutive Mathlib rows: ranges reported as declaring
nothing fell from 108 to 21, with no row losing an answer it had. The 21 that
remain are notation, `deriving instance` and the `foo_def` companion of an
`irreducible_def` — declarations Lean names itself, whose names are in no file.

## `--name` AND `--text` reports "no match" where each half matches

`dt find --name "HasDerivAt" --text "Finset.sum" --limit 10` answers

    no match: every condition matches on its own; drop one

The conjunction is the documented behaviour and the diagnostic is accurate, so
this is not a bug. It is still the wrong answer to the question that was being
asked, which was "which `HasDerivAt` lemma is about a `Finset.sum`". What the
user wants at that point is not "drop one" but the rows that matched the
*names* condition ranked by how well they match the text — the AND is a filter
where a ranking would do. A `--rank` or `--soft` mode, or simply falling back
to a ranked union when the intersection is empty and saying so, would turn a
dead end into an answer. (The lemma actually wanted, `HasDerivAt.sum`, is
indexed and was found on the second try by `--name sum` alone.)

## Staleness line reappears after every `lake build`

Working in a Lean project means rebuilding constantly, and every `dt` call
after a rebuild prints

    dt: project was rebuilt since it was indexed; rows may be missing — dt refresh project

on stderr. It is correct, but during an editing session it fires on nearly
every invocation, and `dt refresh project` (2185 declarations, 494871 rows) is
too slow to run after each build. Either the warning should be rate-limited
per project per session, or the check should compare what actually changed
(the set of `.olean` mtimes against the indexed modules) rather than the fact
that a build happened at all.

Fixed in 0.48.0.  A search, and `dt show`, now read the `.ilean` of every
module compiled since the index was written: its `decls` gives each declared
name with its lines.  When each of them has a row in that module at those
lines, the rebuild added nothing a search could miss and the line is not
printed.  A new, renamed or moved declaration still prints it, and so does a
rebuild whose modules cannot be read.  On a copy of the transformer build,
touching every `.olean` but `CRASP/Frame` (which declares four names the index
lacks) and `Perspective/Section1_Antipodal` (which the root does not import)
prints nothing; touching `Frame` prints the line.  A statement edited in place
on the same lines goes unreported; `dt status` still marks the source stale,
and `dt refresh` still re-reads it.

## From the transformer session (2026-09-16)

- `dt find` with a lambda in the shape fails: `dt find 'Filter.Tendsto (fun _ => -_)
  Filter.atTop Filter.atBot'` answers "no match: `fun` is
  `Lean.Compiler.LCNF.Code.fun` in the index … and that matches nothing either".
  A `fun` in a pattern should either be matched structurally or be rejected with
  a message that says patterns cannot contain binders — not silently resolved to
  an unrelated LCNF constant.
- The AND-semantics message is still misleading: `dt find --name "div_le_div_iff"
  --in Mathlib.Algebra.Order.Field` answers "no match: every condition matches on
  its own; drop one". Dropping `--in` found the lemma in
  `Mathlib.Algebra.Order.GroupWithZero.Basic`. It would help to name *which*
  module prefixes the `--name` hits actually live in.
- `dt: project was rebuilt since it was indexed` appears on stderr after every
  `lake build`, on every subsequent `dt` call, even for Mathlib-only queries that
  cannot be affected by the project index.

Fixed in 0.27.0.

**The lambda.** `fun` is a word, so it was read as a constant, and the only
thing in the index whose name ends that way is `Lean.Compiler.LCNF.Code.fun`.
Nothing about the report is about the compiler; that resolution was the last
step of a search that had already lost the pattern.

A lambda is a binder, and `Shape` is read off a statement with every binder
stripped — there is nothing in the index for the inside of one to be matched
against. So a lambda is now read as the `_` it honestly is, and the slot it
filled is left where it stood: the pattern becomes
`Filter.Tendsto _ Filter.atTop Filter.atBot`, and the third row is
`Filter.tendsto_neg_atTop_atBot`, which is the lemma. The lambda runs to the
end of the group that encloses it, which is Lean's own rule, so
`Finset.sum _ (fun i => f i) = _` keeps its `= _`. An arrow counts as a binder
even with the keyword left off: `(x => -x)` used to read `=` as `Eq`, and since
`=` binds loosest the whole pattern became a search for equations.

It is not silent. The read is announced on stderr, before the rows and
whatever `--verbose` says, because the answer below is to a looser question
than the one that was asked:

    dt: `fun _ => - _` read as `_` — the index is keyed on shapes with every
    binder stripped, so a lambda matches any argument

**The AND message.** "Drop one" is right and useless when the one to drop is
`--in`: the reader knows the lemma exists and guessed wrong about where it is
kept, and the guess is what needs correcting. Dropping the module prefix and
counting the modules that answer costs one query and says the whole of it:

    no match: drop --in — without it the rest matches in Mathlib.Data.Int.Init (4),
    Mathlib.Algebra.Order.Group.Unbundled.Basic (3),
    Mathlib.Algebra.Order.GroupWithZero.Basic (3)

Four modules at most, and the line falls back to the old one when the query
named no module or when dropping it still matches nothing.

**The warning after `lake build`.** The warning was already narrowed to the
sources an answer drew on — but an empty answer draws on none, and "none"
meant "every source", so every failed Mathlib search ended in a line about the
project. A query that says where it is looking can be taken at its word:
`--source` says it outright, `--in Mathlib.Order` says it by prefix and the
index resolves the prefix for the price of one row. A query that restricts
nothing still warns about everything, and so does an `--in` that matches
nothing — a prefix with no rows is exactly what a stale source looks like.

## 0.27.0, from the transformer project

**`--text` once only.** `dt find --text summable --text monotone` is rejected
with `the argument '--text <WORDS>' cannot be used multiple times`. The other
filters compose — `--name` narrows, `--in` narrows, `--uses` narrows — and the
natural way to narrow a text search is a second word from a different part of
the sentence. `--text` already takes whole words, so either the flag repeats
and the words are ANDed, or the message says `--text takes several words:
--text "summable monotone"` instead of naming a clap rule.

**`--long` is a `find` flag.** `dt show Real.log_sqrt --long` errors with
`unexpected argument '--long' found`, and the tip offers `--config`, which is
not what anyone meant. `show` is the command one reaches for after `find`
printed a truncated type, so it is the command `--long` is asked of. Either
`show` accepts it (and prints the docstring), or the tip says `show` already
prints the full statement and `--long` belongs to `find`.

**The AND message with one condition.** A bare pattern, no other flag:

    $ dt find 'Real.log _ ≤ Real.sqrt _'
    no match: every condition matches on its own; drop one

There is one condition and nothing to drop. The same line comes back for
`--source mathlib` plus a pattern, where the only droppable condition is the
source the reader deliberately named. When the conditions are a shape and
nothing else, the answer is about the shape: whether the head is unknown to
the index, whether it matched with fewer arguments, or whether the sides are
in the other order.

Fixed in 0.28.0.

**`--text` repeats, and the words are ANDed.** `Query.text` is a list of words
rather than one string, which is what the text index made of it anyway:
`fts5` splits a MATCH on whitespace and ANDs the terms, so `--text "summable
monotone"` already meant both words and only the flag disagreed. Now the flag
repeats, several words in one `--text` are the same as one word in each, and
the two rules that were reading the string whole — the domain's `matches` and
the `LIKE` fallback for a build without FTS5 — read it word by word like the
index does. Each word is a condition of its own, so `--text summable --text
zzz` blames `--text zzz` rather than the combination.

**`dt show --long` is taken and answered.** `show` already prints the whole
declaration, docstring and proof included, so there is nothing for `--long` to
add — but refusing it costs a round trip to learn that, and clap's tip for the
refusal offered `--config`. The flag is accepted, hidden from `--help`, and
says on stderr where it belongs:

    dt: `--long` belongs to `dt find`; `show` prints the whole declaration
    anyway, source and all

**A pattern is diagnosed as a pattern.** The conditions a shape is taken apart
into — one `--concl`, one per named argument — are probes, not flags, and
"drop one" is an answer about flags. When the shape matches nothing with every
flag dropped, the shape is what the answer is about, and three near misses are
worth one query each:

    $ dt find 'Finset.sum _ _ ≤ Finset.card _'
    no match: nothing has that shape; the same two sides the other way round do

    $ dt find 'Real.exp _ ∣ Real.exp _'
    no match: nothing has that shape; those arguments go together under
    `HasDerivAt`, `HasStrictDerivAt`, `LE.le`

    $ dt find 'Real.log _ ≤ Real.sqrt _'
    no match: nothing has that shape; each of `Real.log`, `Real.sqrt` matches
    without the others

The nearest one only: each is a rewrite to try, and they are offered in the
order of how little they change. The head that is unknown to the index needs
no new line — a constant that is nowhere a head is a barren condition and was
already named as one. A pattern that fails only *with* a flag is still a
combination, because there the flag is the thing to drop.

## 0.28.0, from the transformer project

**A pattern with `--name` blames the combination when the conclusion is an
`Iff`.**

    $ dt find 'List.Sublist _ _' --name sublist_cons_iff
    no match: every condition matches on its own; drop one

`List.sublist_cons_iff` is `l <+ a :: l' ↔ …`: its conclusion head is `Iff`,
so the shape can never match it, and no flag is worth dropping. The row the
name finds is already in hand; the message could say what its conclusion is —
"`--name sublist_cons_iff` finds `List.sublist_cons_iff`, whose conclusion is
`_ ↔ _`; the pattern is matched against the conclusion" — or `find` could match
a relation pattern against either side of an `Iff`, which is where rewriting
lemmas keep it.

**`--in <module>` lists what the compiler generated.**
`dt find --source project --in Transformer.CRASP.PiecewiseTestable` answers
with `PT.ctorIdx` among the first ten rows, and a module with inductives also
gives `*.elim`, `ctorElim`, `ctorElimType` and `*.congr_simp`. Nobody writes
those names; they push the declarations of the file off the first page, and
there is no flag to hide them. Either they are hidden by default (with
`--generated` to ask for them), or they are ranked after everything written by
hand.

**`--text` does not search module docstrings, and does not say so.**
`dt find --source project --text typo` answers `no match: --text typo matches
nothing on its own`, although the module docstring of
`Transformer.CRASP.PiecewiseTestable` has a paragraph headed "A typo." Module
headers are where a file explains itself, so they are the first place a word
search should look; if they are out of scope, `--help` and the no-match line
should say that `--text` reads declaration docstrings only.

**No reverse dependencies.** Before changing the signature of
`Transformer.CRASP.PT.depth_toForm` the question is who uses it. `dt deps`
answers the forward question exactly (it lists `PT.depth_toForm` among the
constants `definableL_of_kPiecewiseTestable` rests on), but the reverse one has
no command, and the flag that looks like it answers only for statements:

    $ dt find --source project --uses Transformer.CRASP.PT.depth_toForm
    no match: --uses Transformer.CRASP.PT.depth_toForm matches nothing on its own

That reads as "nothing uses it", which is false, and it sent the search back to
grep. Either `dt rdeps <name>` (or `--used-by`) over the proof constants the
index already has, or the no-match line says that `--uses` reads statements
only and points at the proofs that do mention the constant.

**The staleness line is per source, not per module.** After a `lake build`
that rebuilt four `Transformer.CRASP.*` modules, `dt show
Transformer.CRASP.Form.sat_le` — in `Transformer.CRASP.Basic`, which was not
rebuilt — still ends with `project was rebuilt since it was indexed; rows may
be missing`. The row it printed cannot be missing or stale. This is the mtime
comparison asked for under "Staleness line reappears after every `lake
build`", seen again at 0.28.0.

**`++` in a pattern is read as `+`.** Looking for `List.range'_append`:

    $ dt find "List.range' _ _ _ ++ List.range' _ _ _ = _"
    no match: every condition matches on its own; drop one
    $ dt find "List.take _ _ ++ _ = _"
    List.sum_take_add_sum_drop  ... (List.take i L).sum + (List.drop i L).sum = L.sum
    List.add_sum_eraseIdx       ...

`List.take_append_drop : List.take i l ++ List.drop i l = l` is indexed and
elaborated, and `dt find "HAppend.hAppend _ _ = _" --in
Init.Data.List.TakeDrop` finds it, so the fault is in parsing the notation: the
first two results are sums, which is what `+` would match. Likely the
tokenizer tries `+` before `++`; `+++`, `<++>`, `::` and other notations that
share a prefix may have the same problem. The no-match line makes it worse:
with a pattern and no flags the only "conditions" are the pattern and the
`--elaborated` it implies, so "drop one" is not something the user can act on.

**`dt refresh project` can leave the project stale at once.** Right after a
`lake build`, a commit and `dt refresh project` (495060 rows), with no build or
edit afterwards, every query ended with `project was rebuilt since it was
indexed; rows may be missing`, and `dt status` three minutes later said:

    project  local  true  true  2374  3m ago  430a4c0 (now 245f6a0, stale)

A second `dt refresh project`, again with nothing in between, recorded
`245f6a0` and the warning went away. So the first refresh recorded a revision
that was already out of date when it finished: most likely the revision is
taken before the dump, and the dump itself changes what the revision hashes
(the build of a new module, `PositionalReductionCount`, had been added to the
project just before). Either take the revision after the dump, or have
`refresh` check it again at the end and say so when it moved.

Fixed in 0.29.0.

**`++`, `::` and the other symbols of several characters are one symbol.** The
tokenizer reads the longest notation first (`<:+:`, `<+:`, `<:+`, `<+`, `++`,
`::`), and a pattern is split where Lean would split it: at the loosest
operator, with Lean's precedences and associativity, rather than at the first
relation in the text. So `_ = _ ↔ _ = _` is an `Iff`, `a - b + c` is an
`HAdd` of an `HSub`, and the `∈` of `∑ i ∈ Finset.range n, f i = _` is the
binder's range, not the relation. `∉` is `Not (Membership.mem …)`, as it
elaborates.

    $ dt find "List.range' _ _ _ ++ List.range' _ _ _ = _"
    List.range'_append_1  theorem  Init.Data.List.Range
    List.range'_append  theorem  Init.Data.List.Range

A constant written inside a pattern is named as such in a no-match line (`` `X`
in the pattern ``, not `--uses X`), and when the shape matches but never
together with those constants, that is what the line says.

**A name that finds a declaration of another shape says what its shape is.**
Matching a relation against either side of an `Iff` would make every pattern
two searches and blur what a conclusion is, so the answer is the message, with
the one-character rewrite when the pattern is a side:

    $ dt find 'List.Sublist _ _' --name sublist_cons_iff
    no match: `List.sublist_cons_iff` concludes `Iff` over `List.Sublist Or`,
    and a pattern is matched against the whole conclusion; to match one side
    of it, append ` ↔ _` to the pattern

**Compiler-generated names are hidden unless `--generated`.** `ctorIdx`,
`ctorElim`, `ctorElimType`, `congr_simp`, `ofNat_ctorIdx`, what is under
`brecOn`, and an `elim` whose type is about `ctorIdx` (so `Or.elim` stays). A
search only they answer says so rather than `no match`.

**`dt rdeps <name>`** lists what mentions a declaration, in a proof or in a
statement (marked `*`), grouped by module, with `--in`, `--source`, `--limit`
and `--generated`. `--uses` still reads statements; its no-match line and
`--help` now say so and point at `dt rdeps`.

**`--text` reads declarations, not module docstrings**, and says so in `--help`
and in its no-match line. Module headers are not in the dump, and reading them
would mean a row kind that is not a declaration; that is left out of scope.

**`dt show` is stale only if a shown module was rebuilt.** A local source whose
build moved is let off when the `.olean` of every module `show` printed is
older than the index. A search still warns: what it did not find may be in a
module that was rebuilt.

Fixed in 0.30.0.

**`dt refresh` records the build it read, and says when a build landed while
it read.** The revision was already taken after the dump, when `dt index`
started, and neither the dump (`lake env lean`, which builds nothing) nor the
load writes under `.lake/build/lib`. So the change came from outside. The
likely one here: a session working on dt ran `touch` on
`Transformer/CRASP/Basic.olean` through a probe directory whose `.lake` turned
out to be a symlink to this project's. That changed the build fingerprint
(path, size and mtime of every `.olean`) with no build at all. A `lake build`
still running, or the editor compiling an import, does the same.

What changed in `dt refresh`: the revision of each compiled source it dumps is
taken before the dump and recorded as the index's revision, since those are
the rows it holds. When the refresh ends, the revision is read again, and a
source that moved in between is named then rather than by the next search:

    dt: `project` was rebuilt while it was being read, so the index is already
    behind it — `dt refresh project` once the build has finished

`dt index` on its own still records the revision it finds when it starts.

**`--kind` takes one kind, and a list is blamed as matching nothing.**
Looking for the definitions `Transformer.CRASP.Depth` rests on:

    $ dt find --source project --name CRASP.Affix --kind def,structure,abbrev
    no match: --kind def,structure,abbrev matches nothing on its own

`--uses` takes a comma list, so `--kind` reads as if it does too; here the
whole string is taken as one kind, which no row has, and the answer is the
same line an empty search gives. An unknown kind should be an error naming the
kinds there are (as an unknown `--source` already is), or `--kind` should take
a list like `--uses`. `abbrev` is not among the kinds either: an `abbrev` is
indexed as `def`, which `--help` could say.

Fixed in 0.31.0.

**`--kind` takes a list, and a word that is not a kind is an error.** A comma
list, or the flag repeated, means any of those kinds, and the list is one
condition in a no-match line (`--kind def,structure`). A word that is not a kind
fails before the search, naming the kinds:

    $ dt find --name Affix --kind defs
    dt: no kind `defs`; the kinds are theorem, def, structure, inductive, axiom,
    instance, ctor, opaque, rec, quot (`lemma` is theorem, `abbrev` def, `class`
    structure), and a comma list means any of them

`--help` names the same kinds and the three aliases. `opaque`, `rec` and
`quot` were in the index all along and are now listed.

**`dt show` reads a name with spaces in it as one name.**  Two primes in an
unquoted shell line pair up into a quoted string, so

    $ dt show List.range'_one List.Perm.mem_iff List.mem_range'_1
    dt: List.range_one List.Perm.mem_iff List.mem_range_1 is not in the index; try `dt find --name mem_range_1`

hands `dt` a single argument `List.range_one List.Perm.mem_iff List.mem_range_1`,
and the answer treats it as one missing declaration, suggesting a search for
its last word.  No Lean name contains a space: an argument that does is several
names glued together by the shell, and the primes are gone from them.  The
answer could say so — "an argument with spaces is several names; a prime in an
unquoted shell word starts a quoted string, quote each name that has one" —
instead of suggesting `--name` on a mangled fragment.

Fixed in 0.32.0.

**A name argument with a space in it is refused, and the shell is named.** No
Lean name has whitespace outside `«»`, so `show`, `deps`, `rdeps` and `add`
recognise such an argument as several names joined, and say so rather than
look it up:

    $ dt show List.range'_one List.Perm.mem_iff List.mem_range'_1
    dt: `List.range_one List.Perm.mem_iff List.mem_range_1` is 3 names in one
    argument, and no Lean name has a space: a `'` in an unquoted shell word
    starts a quoted string that runs to the next `'`, joining the words between
    and dropping both primes — pass each name as its own word, in double quotes
    if it has a prime ("List.range'_one")

In a `show` batch the rest of the names are still shown. The words are not
looked up one by one: the primes are gone from them, so a hit would often be a
different lemma (`List.range_one` rather than `List.range'_one`).

---

## `dt show` misses a header that follows an attribute on the same line

    $ dt show List.filter_replicate
    import Init.Data.List.Lemmas

    List.filter_replicate
      theorem  Init.Data.List.Lemmas:2331-2336
      those lines declare nothing: `@[grind =] theorem filter_replicate : (replicate n a).filter p = if p a then replicate n a else [] := by`

The complaint quotes the header it failed to see: the line is
`@[grind =] theorem filter_replicate`, the word before the name is `theorem`,
and the name is the one Lean printed.  The rule from 0.26.0 — "a word at column
zero followed by the name" — reads `@[grind` as that word.  Core writes the
attribute on the header's line throughout `Init` (`@[simp] theorem`,
`@[grind =] theorem`), so this is a class of rows, not one.  An attribute
block `@[...]` at the start of a line (balanced brackets, possibly several:
`@[simp] @[grind] theorem`) should be skipped before looking for the word, as
the modifiers `meta` / `public` already are.  The row still printed the
elaborated type below the complaint, so nothing was lost but the source.

Seen with dt 0.32.0, 2026-09-16.

Fixed in 0.33.0.

**The attribute was not the cause: the line is indented.** In core it reads
` @[grind =] theorem filter_replicate` with a stray space at column zero, and
`@[...]` blocks were already skipped. The column-zero rule is what keeps a
`have` or a nested `def` inside a proof from reading as a header. Within a
declaration range, though, Lean has already said where the declaration starts,
so the first code line of the range may now be indented when it opens with a
known header (`theorem`, `def`, … after attributes and modifiers). Later lines
keep the rule, and so does the "any word followed by the name" reading, where
an indented `exact foo` would otherwise count.

    $ dt show List.filter_replicate
    import Init.Data.List.Lemmas

    List.filter_replicate
      theorem  Init.Data.List.Lemmas:2331-2336

     @[grind =] theorem filter_replicate : (replicate n a).filter p = if p a then …

---

## The index notation `l[i]?` is dropped from a pattern, and its constant cannot be written

    $ dt find '(_ ++ _)[_]? = _' --verbose
    dt: `(_ ++ _)[_]? = _` read as conclusion Eq, 2 argument(s), operator `=`
    ENat.natCast_one  theorem  Mathlib.Data.ENat.Basic
      ↑1 = 1
    Cardinal.ofENat_one  theorem  Mathlib.SetTheory.Cardinal.ENat
      ↑1 = 1

The lemma asked for is `List.getElem?_append_right`,
`(l₁ ++ l₂)[i]? = l₂[i - l₁.length]?`.  The postfix `[_]?` is neither in the
notation table nor reported: the left side is read as nothing, the pattern
widens to `_ = _`, and the rows are whatever equations rank first.  That is
the widening the 0.23.0 rule ("narrow rather than widen, and name the part")
was written against; `_[_]? = _` alone does the same.  `l[i]`, `l[i]!` and
`xs[i]'h` are presumably in the same position.

The advice the rule gives for an unknown symbol — write the constant it stands
for — cannot be followed here, because the constant's name contains `?`:

    $ dt find 'GetElem?.getElem? (_ ++ _) _ = _'
    no match: `.getElem` in the pattern reads as nothing here; searching without
    it would answer a wider question — write the constant it stands for instead,
    or drop that part of the pattern and give it as --uses

The tokenizer splits `GetElem?.getElem?` at each `?`.  Either `?` (and `!`)
belong to an identifier when they follow one, as in Lean, or `[_]?` is a
bracket that stands for `GetElem?.getElem?` (and `[_]` for `GetElem.getElem`,
`[_]!` for `GetElem?.getElem!`).  `--name getElem?_append` found the lemma.

Seen with dt 0.33.0, 2026-09-16.

Fixed in 0.34.0.  Both halves, since each is how Lean reads it.

A name may have `?` and `!` in it, as Lean's do: `GetElem?.getElem?`,
`List.head?` and `Option.get!` are one name each.  Before, `List.head? _ = _`
was quietly a search for `List.head`.  Only after a name, so `_` stays a
wildcard, and `!=` is still the `≠` it is typed for.

Index notation is expanded the way Lean's macros expand it:

    xs[i]      GetElem.getElem xs i
    xs[i]'h    GetElem.getElem xs i h
    xs[i]?     GetElem?.getElem? xs i
    xs[i]!     GetElem?.getElem! xs i

each as one term in parentheses, so it binds tighter than any operator and
than an application: `l[i] + 1` is an addition, and `Nat.succ l[i]` is
`Nat.succ`.  As in Lean, a `[` indexes only a term it is written against --
`f [i]` still applies `f` to a list -- so the lexer keeps whitespace until the
expansion has read it.

    $ dt find '(_ ++ _)[_]? = _'
    BitVec.getElem?_zero_ofNat_one  theorem  Init.Data.BitVec.Lemmas
      ∀ {w : Nat}, (1#(w + 1))[0]? = some true
    List.getElem?_nil  theorem  Init.Data.List.Lemmas
      ∀ {α : Type u_1} {i : Nat}, [][i]? = none

The rows now answer the question asked, as far as a shape reaches.  The `++`
does not reach: a shape is a conclusion head and the heads of its arguments,
and what an index is taken of is a level below that.
`List.getElem?_append_right` is row 185 of that search, and row 8 with the
`++` given as a condition:

    $ dt find '(_ ++ _)[_]? = _' --uses HAppend.hAppend
    List.getElem?_concat_length  theorem  Init.Data.List.Lemmas
    Array.getElem?_append_left   theorem  Init.Data.Array.Lemmas
    …
    List.getElem?_append_right   theorem  Init.Data.List.Lemmas

A name that deep already becomes a `--uses` condition, and notation that deep
could too; `|_ + _|` has lost its `+` the same way since 0.23.0.  That changes
every pattern with nested notation, so it is left to an entry of its own.

Written as the lemma states it, `(l₁ ++ l₂)[i]? = l₂[i - l₁.length]?` is still
`no match`, for a different reason: `l₁.length` is field notation on a
variable, and read as a name it names nothing.

---

## Notation inside a side is read as nothing, and a `-` before a term is a subtraction

The rest of the entry above.  A shape is a conclusion head and the heads of
its arguments, and notation below that was dropped without a word: in
`(_ ++ _)[_]? = _` the `++` said nothing, and `List.getElem?_append_right`
was row 185.  A name that deep becomes a `--uses` condition; notation, which
is a name spelled differently, did not, and `--verbose` did not say so:

    $ dt find '(_ ++ _)[_]? = _' --verbose
    dt: `(_ ++ _)[_]? = _` read as conclusion Eq, 2 argument(s), operator `=`

Reading notation wherever it is needs `-` read right, and it was not.  Lean
has two: `a - b` is `HSub.hSub` at 65, `-a` is `Neg.neg` at 75.  Every `-`
was the subtraction, so a side that starts with one was read by an operator
it does not have:

    $ dt find -v '_ = -_ * _'
    dt: `_ = -_ * _` read as conclusion Eq, 2 argument(s), operator `=`
    Nat.zero_sub_one  theorem  Init.Data.Nat.Basic
      0 - 1 = 0

and a pattern that starts with one could not be typed at all:

    $ dt find '-_ * _ = _'
    error: unexpected argument '-_' found

Seen with dt 0.34.0, 2026-09-16.

Fixed in 0.35.0.

**Notation as a condition.**  Notation anywhere in the pattern becomes a
`--uses` condition, as a name there does, and `--verbose` lists the
conditions the pattern became:

    $ dt find '(_ ++ _)[_]? = _' --verbose
    dt: `(_ ++ _)[_]? = _` read as conclusion Eq, 2 argument(s), operator `=`, --uses HAppend.hAppend
    List.getElem?_concat_length  theorem  Init.Data.List.Lemmas
    …
    List.getElem?_append_right   theorem  Init.Data.List.Lemmas
    …
    10 result(s)

Row 8 of 10.  Three things are left out.  A head the shape already has is
in every row the shape matches, so as a condition it rules nothing out and
is one more name to blame when the answer is empty: `|_ + _| ≤ |_| + |_|`
has no conditions.  A bracket counts once it closes, so the `|` in
`{x | x ≤ 0}` is not an absolute value.  And the relation a binder ranges
with is not always in the type: `∑ i ∈ s, f i` is `Finset.sum s f`, with no
membership in it, and a condition asking for one would rule out the lemma
the pattern was copied from.

**Negation.**  A `-` with no term before it -- at the start of a side, after
an operator, just inside a bracket -- is `Neg.neg`, and binds as Lean binds
it: `-a * b` is a product of `-a`, and `-x ^ 2` is the negation of a power.

    $ dt find -v '_ = -_ * _'
    dt: `_ = -_ * _` read as conclusion Eq, 2 argument(s), operator `=`, --uses Neg.neg
    Complex.I_mul_I  theorem  Mathlib.Basic.Complex.Basic
      Complex.I * Complex.I = -1
    Int.neg_eq_neg_one_mul  theorem  Init.Data.Int.Lemmas
      ∀ (a : Int), -a = -1 * a

The first row has its `-` on the other side: a condition is looked for
anywhere in the statement, not where the pattern put it.

**The command line.**  `dt find '-_ * _ = _'` works, wherever the pattern is
among the flags.  Taking every argument that starts with `-` as a possible
pattern took misspelt flags too (`--elaborted` searched for itself), so the
line is read as written first.  Only if that fails is an argument of `find`
that no flag is spelled like -- a `-` and then anything but letters -- read
again from behind a `--`.  A misspelt flag still gets the error, and the
suggestion, it got before.

---

## An argument of a prefix pattern is read a token at a time

Found while checking 0.35.0.  The arguments of a prefix pattern were every
name, literal and `_` after its head, so a group in parentheses was as many
arguments as it had names in it, and its notation was lost:

    $ dt find -v 'HasDerivAt (fun x => x ^ 2) (2 * x) x'
    dt: `HasDerivAt (fun x => x ^ 2) (2 * x) x` read as conclusion HasDerivAt, 4 argument(s), `x` as `_`, --uses HMul.hMul
    no match: the shape matches, but nothing of that shape mentions `HMul.hMul`; …

    $ dt find 'Filter.Tendsto _ Filter.atTop (nhds 0)'
    no match: nothing has that shape

The second is as plain a `Tendsto` as there is.  A side had the same fault
the other way: its head was the loosest notation on it, and a `⁻¹` on an
argument was looser than nothing, so `Real.log x⁻¹` was read as an inverse:

    $ dt find 'Real.log x⁻¹ = -Real.log x'
    no match: the shape matches, but nothing of that shape mentions `Real.log`; …

Seen with dt 0.35.0, 2026-09-16.

Fixed in 0.36.0.  An argument is a term: a name, a `_`, a literal, or a
bracket and what it encloses, with a postfix operator after it.  Each is
read by its head the way a side is, so `(2 * x)` is `HMul.hMul`, `(nhds 0)`
is `nhds` and `l[i]` is `GetElem.getElem`.  A name that heads an argument
is not also a condition, as the name that heads a side is not.

An application binds its arguments as tightly as a postfix operator binds
(Lean's `max`), and the operator binds to the term before it.  So a `⁻¹`
heads a term only if nothing is applied there: `(Real.log x)⁻¹` is an
inverse and `Real.log x⁻¹` a logarithm.

    $ dt find 'Real.log x⁻¹ = -Real.log x'
    Real.log_inv  theorem  Mathlib.Analysis.SpecialFunctions.Log.Basic
      ∀ (x : ℝ), Real.log x⁻¹ = -Real.log x
    1 result(s)

    $ dt find 'HasDerivAt f (-Real.sin x) x'
    Real.hasDerivAt_cos  theorem  Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

`Filter.Tendsto _ Filter.atTop (nhds 0)` has 365 rows, `nhds ⊤` and
`nhds 1` among them: the `0` is below the shape, and a literal is never a
condition.  `HasDerivAt (fun x => x ^ 2) (2 * x) x` has 62, with
`hasDerivAt_pow` 26th; the `^` is inside a lambda, which is read as `_`
(0.27.0), and given as `--uses HPow.hPow` it makes the lemma 8th of 21.

---

## `dt show` rejects the `--source` that `find` takes

`find` narrows to a source with `--source`, so the same flag on the `show` that
follows it reads as the natural continuation.  It is an error there, and the
tip clap prints — pass it as a value after `--` — is wrong for this command:

    $ dt find --source project --name altPlus --kind def
    Transformer.CRASP.altPlus  def  Transformer.CRASP.Alternating
    $ dt show --source project Transformer.CRASP.altPlus
    error: unexpected argument '--source' found

      tip: to pass '--source' as a value, use '-- --source'

A full name already fixes the source, so `show` needs no filter.  Either accept
`--source` and check the name against it (an error when the name is not in
that source says something useful), or say in the error that `show` looks the
name up in every source.

Seen with dt 0.36.0, 2026-09-16.

Fixed in 0.38.0.  `show` takes `--source` and shows the row that source has.
That is a filter and not only a check: 426 names are in more than one row of
the index, nine of them in more than one source, and `AddSubgroup.inertia_mono`
is in Mathlib and, read as text, in FLT.  Without the flag the compiled row
answers, as it always has; with it the text one does:

    $ dt show --source flt AddSubgroup.inertia_mono
    -- source `flt` is not importable; `dt add AddSubgroup.inertia_mono` copies it instead

    AddSubgroup.inertia_mono  [text]
      theorem  Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup:11-12
    …

A source without the name says which sources have it, and a batch goes on past
that miss as it goes on past any other:

    $ dt show --source project AddSubgroup.inertia_mono
    dt: AddSubgroup.inertia_mono is in `flt`, `mathlib`, not in `project`

    $ dt show --import-only --source mathlib Real.exp_le_exp List.length
    import Mathlib.Analysis.Complex.Exponential
    dt: List.length is in `core`, not in `mathlib`

The stale-index warning after a miss checks that source alone, the one the
name was looked for in, and a source that is not configured is refused as
`find` refuses it.

---

## Field notation is read as a name, and names nothing

Left over from 0.34.0.  Lean states most of its library with field notation
-- `l.length` is `List.length l`, the namespace taken from the type of `l` --
and a pattern copied out of a statement has it wherever the statement did.
`l₁.length` was read as a constant called that:

    $ dt find -v '(l₁ ++ l₂)[i]? = l₂[i - l₁.length]?'
    dt: `(l₁ ++ l₂)[i]? = l₂[i - l₁.length]?` read as conclusion Eq, 2 argument(s), operator `=`, `i`, `l₁`, `l₂` as `_`, --uses HAppend.hAppend HSub.hSub l₁.length
    no match: `l₁.length` in the pattern matches nothing on its own

A field after a bracket was not even that, and a field that heads the
pattern was its conclusion:

    $ dt find 'l[i]?.getD d = _'
    no match: `.getD` in the pattern reads as nothing here; …

    $ dt find -v 'l.Sublist (l ++ m)'
    dt: `l.Sublist (l ++ m)` read as conclusion l.Sublist, 1 argument(s), `l`, `m` as `_`
    no match: --concl l.Sublist matches nothing on its own

Seen with dt 0.36.0, 2026-09-16.

Fixed in 0.37.0.  A field is its name in whichever namespace has one, applied
to the term it is written on: `l₁.length` is `.length` applied to `_`, and
`.length` names `List.length`, `Array.length` and every other constant whose
last component is `length`, in the case it is written in.

    $ dt find -v '(l₁ ++ l₂)[i]? = l₂[i - l₁.length]?'
    dt: `(l₁ ++ l₂)[i]? = l₂[i - l₁.length]?` read as conclusion Eq, 2 argument(s), operator `=`, `i`, `l₁`, `l₂` as `_`, --uses .length HAppend.hAppend HSub.hSub
    List.getElem?_append_right  theorem  Init.Data.List.Lemmas
      ∀ {α : Type u_1} {l₁ l₂ : List α} {i : Nat}, l₁.length ≤ i → (l₁ ++ l₂)[i]? = l₂[i - l₁.length]?
    1 result(s)

    $ dt find 'l.Sublist (l ++ m)' --limit 2
    List.sublist_append_right  theorem  Init.Data.List.Sublist
      ∀ {α : Type u_1} (l₁ l₂ : List α), l₂.Sublist (l₁ ++ l₂)
    List.sublist_append_left  theorem  Init.Data.List.Sublist
      ∀ {α : Type u_1} (l₁ l₂ : List α), l₁.Sublist (l₁ ++ l₂)
    2 shown, more match; refine or --limit

The flags take the same name: `--concl .Nodup`, `--uses .length`.

**What a field is written on.**  The word before a `.` is a term when it is a
bound variable or in lower case -- `l`, `xs`, `hab` -- and a namespace when it
is capitalised or in camel case, as namespaces are: `List.length`,
`intervalIntegral.integral_const`.  The few namespaces in lower case, `lp` and
`spectrum` among them, read as fields now, and still find their constants
among others.  A numbered field, the `1` of `p.1`, has no name and is `_`.  A
word in lower case with no field on it, the `xs` of `xs ++ ys`, is still read
as a constant.

**`(f a) b` is `f a b`**, which is how a field takes the rest of its
arguments: `l.Sublist (l ++ m)` has two, and the second is headed by `++`.

**Case.**  A field is a `GLOB` suffix in the index and not a `LIKE` one, which
ignores case, and a `--uses` is not checked again after the SQL: `.nodup` does
not find `List.Nodup`.

A lambda is reported as it was written again, which it had not been since
0.34.0: `fun i => l[i]` was printed as the application its index expands to.

---

## Rows that share a name are given each other's dependencies

Found while making `show --source` take the row a source has.  The index read
a row's constants and dependencies by the row's name, so a name in several
rows gave every one of them the lists of all.  `RestrictedProduct.singleAddMonoidHom`
is in Mathlib, with fourteen dependencies read off its proof term, and in FLT,
with three more a scanner guessed from the text, and `deps` gave all seventeen
as exact:

    $ dt deps RestrictedProduct.singleAddMonoidHom
    RestrictedProduct.singleAddMonoidHom
    depth 1 (17)
      core: DecidableEq
      mathlib: AddMonoid AddMonoid.toAddZeroClass AddMonoidHom.mk AddSubmonoidClass AddZero.toZero
        AddZeroClass.toAddZero Filter.cofinite Pi.single Pi.single_add RestrictedProduct
        RestrictedProduct.instAddMonoidCoeOfAddSubmonoidClass RestrictedProduct.single
        Set.finite_singleton SetLike SetLike.coe ZeroHom.mk

`Pi.single`, `Pi.single_add` and `Set.finite_singleton` are the guesses.  426
names are in more than one row, and the same lists make the closure `dt add`
copies and rank the rows of `find`.

Seen with dt 0.38.0, 2026-09-16.

Fixed in 0.39.0.  A row's lists are read by its id, and each row keeps its own:

    $ dt deps RestrictedProduct.singleAddMonoidHom
    RestrictedProduct.singleAddMonoidHom
    depth 1 (14)
      core: DecidableEq
      mathlib: AddMonoid AddMonoid.toAddZeroClass AddMonoidHom.mk AddSubmonoidClass AddZero.toZero
        AddZeroClass.toAddZero Filter.cofinite RestrictedProduct
        RestrictedProduct.instAddMonoidCoeOfAddSubmonoidClass RestrictedProduct.single SetLike
        SetLike.coe ZeroHom.mk

`find` reads them only for the rows that match the shape.  Neither change
moved the time of a search or of a 4844-declaration closure, and the 104
patterns of the regression sweep find what they found before.

Not fixed: two instances in Mathlib's `CategoryTheory.Abelian` are declared in
two modules each, and both rows of each have one line range, because the dump
takes the constant from its module and looks the range up by name.

## `false` and `true` in a pattern match nothing; `Bool.false` does

Looking for `count false l + count true l = l.length` on `List Bool`:

    $ dt find 'List.count false _ + List.count true _ = _'
    no match: `false` in the pattern, `true` in the pattern match nothing on their own
    $ dt find 'List.count Bool.false _ + List.count Bool.true _ = _'
    List.count_false_add_count_true  theorem  Mathlib.Data.Bool.Count
      ∀ (l : List Bool), List.count false l + List.count true l = l.length

The row itself prints the constants as `false` and `true`, so the spelling the
result shows is the one the pattern rejects.  Same family as `inner` having to
be spelled `Inner.inner`: resolve `false`/`true` (and other constructors that
Lean opens by default) the way the elaborator does, or name the qualified
spelling in the failure message.

Seen with dt 0.39.0, 2026-09-16, transformer session.

Fixed in 0.40.0, by the first repair: a bare word is resolved wherever it
stands in the pattern, not only where it heads something.  0.21.0 resolved
`inner` because it headed a side; `false` here is an argument of an argument,
so it became `--uses false`, and the resolver never looked at those.  Now it
does, by the same rule -- the commonest head symbol whose last component is the
word -- and says so on stderr:

    $ dt find 'List.count false _ + List.count true _ = _'
    dt: `false` read as `Bool.false`
    dt: `true` read as `Bool.true`
    List.count_false_add_count_true  theorem  Mathlib.Data.Bool.Count
      ∀ (l : List Bool), List.count false l + List.count true l = l.length
    List.count_true_add_count_false  theorem  Mathlib.Data.Bool.Count
      ∀ (l : List Bool), List.count true l + List.count false l = l.length

The rest of what the Prelude exports comes with it, with no table to keep:
`Option.getD none _ = _` reads `none` as `Option.none`, and `max`, `min`,
`some`, `default` and `decide` are found the same way.  A word inside a side is
counted over heads too, because heads are what the index counts without a scan
of `uses`, and the constant a word names one argument down is the one it names
at the top of other statements: `Bool.false` is a head in 297 rows.

The second repair was already there once the first reached these words.  When
the resolved pattern fails as well, the failure names the spelling:

    $ dt find 'List.count false _ * List.count true _ = _'
    no match: `false` is `Bool.false` in the index — Lean prints an exported
    name without its namespace — and that matches nothing either; also
    `Std.Do.ExceptConds.false`, `Std.Sat.AIG.Decl.false`

The lookup still runs only after the search as written found nothing, so a
pattern that answers costs what it did, and one that fails pays one scan of
`decl` per bare word, 0.16 s on the probe's index.  The 104 patterns of the
sweep answer exactly as before.

## A word in lower case is read as a constant unless a field is written on it

0.15.0 reads one letter as a variable, and 0.37.0 reads a word a field is
written on as one.  Every other word in lower case is a constant, and the
names people give lists, hypotheses and accumulators are words:

    $ dt find 'xs ++ ys = _'
    no match: `xs` in the pattern, `ys` in the pattern match nothing on their own
    $ dt find 'hf.comp hg = _'
    no match: `hg` in the pattern matches nothing on its own

The same word is read two ways in one pattern.  `xs.length` makes `xs` a
variable, and the `xs` next to it is still a constant:

    $ dt find '(xs ++ ys).length = xs.length + ys.length'
    no match: `xs` in the pattern, `ys` in the pattern match nothing on their own

And since 0.40.0 resolves every bare word, a variable that shares its name
with a field somewhere in Mathlib is read as that field:

    $ dt find 'List.reverse (as ++ bs) = _'
    no match: `as` is `CategoryTheory.Discrete.as` in the index — Lean prints an
    exported name without its namespace — and that matches nothing either; also
    `FundamentalGroupoid.as`, `CategoryTheory.Quotient.as`

Seen with dt 0.40.0, 2026-09-16.

Fixed in 0.41.0, in two parts.  The first is syntax: a word a field is written
on is a variable wherever it stands, so the pattern with `xs.length` in it
reads its `xs ++ ys` as `_ ++ _` and answers as written.

The second is a second look, after a search found nothing, like 0.40.0's.  A
word the index has by that spelling -- a row called it or mentioning it --
means itself, so `deriv`, `id` and `closure` are never read as anything else.
A word Lean prints for a constant is that constant.  A word in lower case that
is neither is a variable, and stderr says so:

    $ dt find 'List.reverse (as ++ bs) = _'
    dt: `as`, `bs` read as `_` — no constant in the index is called that
    List.reverse_concat'  theorem  Mathlib.Data.List.Basic
      ∀ {α : Type u} (l : List α) (a : α), (l ++ [a]).reverse = a :: l.reverse
    $ dt find 'hf.comp hg = _'
    dt: `hg` read as `_` — no constant in the index is called that
    Real.log_comp_exp  theorem  Mathlib.Analysis.SpecialFunctions.Log.Basic
      Real.log ∘ Real.exp = id

"Lean prints for a constant" is now counted, not guessed from frequency.  A
row counts for `N.w` only if its type says `w` as a name of its own, never says
`.w`, and never binds `w`: `(val : α)`, `[inst : Monoid α]` and
`{ neg := y }` are where the remaining false readings came from.  On the
probe's index, about 130 names people give variables (`as`, `xs`, `hf`,
`init`, `step`, `val`, `inst`, `acc`, `key`, ...) get no candidate at all, and
what the Prelude and Mathlib export keeps its count: `Bool.false` 297 rows,
`Inner.inner` 326, `Option.none` 773, `Max.max` 687, `SupSet.sSup` 417.  The
"also" list after an unqualified failure shrinks to what is printed bare, which
for `inner` is nothing: `Std.DTreeMap.Internal.Impl.inner` was never a reading.

What this gives up: a word Lean prints with its namespace is no longer guessed
at.  `succ n ≤ m ↔ n < m` used to be about `Order.succ`, the commonest `succ`;
now `succ` is a variable, and the line on stderr says to spell the one meant.
A pattern copied from a goal never has that word in it, because the goal said
`Order.succ` or `n.succ`.

## A pair `(a, b)` is read as parentheses, and `Prod.mk` is not searched for

Parentheses name nothing, and the comma inside them is punctuation, so a pair
is whatever its first element is.  `(a, b)` is `_`, and a pattern about pairs
is a pattern about anything:

    $ dt find '(a, b) = (c, d) ↔ a = c ∧ b = d'
    Nat.dvd_antisymm_iff  theorem  Mathlib.Data.Nat.Basic
      ∀ {m n : ℕ}, m = n ↔ m ∣ n ∧ n ∣ m
    $ dt find 'Prod.fst (a, b) = a'
    LucasLehmer.X.zero_fst  theorem  Mathlib.NumberTheory.LucasLehmer
      ∀ {q : ℕ}, 0.1 = 0

The index has it: `(p.1 ⊔ q.1, p.2 ⊔ q.2)` is stored with `Prod.mk` as its
head, 910 rows have it as one, and `Prod.mk a b = _` finds `Prod.mk.eta`.

Seen with dt 0.41.0, 2026-09-16.

Fixed in 0.42.0.  Parentheses with a comma at their top level are a pair,
headed by `Prod.mk` wherever they stand: as a side, as an argument, and as a
condition when they are further in.

    $ dt find 'Prod.fst (a, b) = a'
    Lean.Omega.Prod.fst_mk  theorem  Init.Omega.Int
      ∀ {α : Type u_1} {x : α} {β : Type u_2} {y : β}, (x, y).fst = x
    $ dt find '(a, b) = _'
    Prod.mk.eta  theorem  Mathlib.Data.Prod.Basic
      ∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p

The pattern from the report now finds only statements about pairs, with
`Prod.mk_inj` fifth, after four of the same shape about `1` and `0`.  A comma
that ends a binder is not a pair: `(∀ x, p x)` and `(∑ i ∈ s, f i)` group as
before.  `⟨a, b⟩` still names nothing, because which structure it builds is
the one thing it does not say.

## `dt rdeps` does not accept a field

`find --uses` reads `.length` as any constant ending in it; `dt rdeps` wants
the whole name, and says nothing about what it could have been:

    $ dt rdeps .integral_mono_on
    dt: .integral_mono_on is not in the index
    $ dt rdeps .deriv_exp
    dt: .deriv_exp is not in the index

`intervalIntegral.integral_mono_on` is the only constant ending in
`.integral_mono_on`; `.deriv_exp` ends two, `Real.deriv_exp` and
`Complex.deriv_exp`, and `.length` fifty-two.

Seen with dt 0.42.0, 2026-09-16.

Fixed in 0.43.0.  A field is the one declaration that ends in it, and the
answer's first line names it; when several end in it, the error lists them,
the ones most statements mention first:

    $ dt rdeps .integral_mono_on
    intervalIntegral.integral_mono_on: used by 5
    $ dt rdeps .length
    dt: .length ends 52 declarations; name one: List.length,
      SimpleGraph.Walk.length, RelSeries.length, Module.length, …, and 42 more

Not every declaration it names, as `find --uses` reads it: a refactor changes
one, and the users of fifty-two `length`s have nothing in common.  A name
without a dot is still the whole name, so `dt rdeps exp_le_exp` still says
it is not in the index.

## `deps` and `add` do not accept `--source`

`show --source` picks the row a source has, since 0.38.0, and then points at
a command that cannot:

    $ dt show --source flt AddSubgroup.inertia_mono
    -- source `flt` is not importable; `dt add AddSubgroup.inertia_mono` copies it instead
    $ dt add AddSubgroup.inertia_mono
    imports
      import Mathlib.Algebra.Group.Subgroup.Basic
    Nothing to copy: every dependency is reachable by an import.
    $ dt add --source flt AddSubgroup.inertia_mono
    error: unexpected argument '--source' found
    $ dt deps --source flt AddSubgroup.inertia_mono
    error: unexpected argument '--source' found

`dt add` answers for the Mathlib row, which is right without the flag, and
there is no way to ask for the FLT one the hint was about, or for its
dependencies.

Seen with dt 0.43.0, 2026-09-16.

Fixed in 0.44.0.  `deps` and `add` take `--source` and start from the row
that source has, as `show` does, with the same error when it has none; the
walk below the root is unchanged, since a dependency is the constant a proof
names and the default row is still the one it means.  `show` now hints the
command that copies the row it showed:

    $ dt show --import-only --source flt AddSubgroup.inertia_mono
    -- source `flt` is not importable; `dt add --source flt AddSubgroup.inertia_mono` copies it instead
    $ dt add --source flt AddSubgroup.inertia_mono
    imports
      import Mathlib.Algebra.Group.Subgroup.Defs
    to materialize: 1 declaration(s) in 1 file(s), 2 lines, tree depth 0
    $ dt deps --source flt AddSubgroup.inertia_mono
    AddSubgroup.inertia_mono  [text]
    -- approximate: this source is indexed as text, so dependencies are guessed
    depth 1 (1)
      mathlib: AddSubgroup
    $ dt add --source core AddSubgroup.inertia_mono
    dt: AddSubgroup.inertia_mono is in `flt`, `mathlib`, not in `core`

## Two modules that declare one name get one line range

Lean imports a theorem declared in two modules when the two agree, and Mathlib
has two: `CategoryTheory.Abelian.instIsStableUnderBaseChangeEpimorphisms` and
its `Cobase` twin are in `Abelian.CommSq`, at lines 43–47, and in
`Abelian.Monomorphisms`, at 30–38.  Both rows of each have the `CommSq` range:

    $ sqlite3 .discrtree/index.db "select module, line_start, line_end from decl
        where name = 'CategoryTheory.Abelian.instIsStableUnderCobaseChangeMonomorphisms'"
    Mathlib.CategoryTheory.Abelian.CommSq|43|44
    Mathlib.CategoryTheory.Abelian.Monomorphisms|43|44

The dump takes each constant from the module that declares it, then asks
`findDeclarationRanges?` by name, and that answers from the first module the
name was imported from.  A project of two modules shows it:

    -- Dup/A.lean: `theorem same` at line 3; Dup/B.lean: at line 8
    Dup.same Dup.A 3 4
    Dup.same Dup.B 3 4

`dt show` then prints the wrong lines of `Monomorphisms`, and `dt add` would
copy them.

Seen with dt 0.44.0, 2026-09-16.

Fixed in 0.45.0.  The dump reads the range from the entries of the module
that declares the constant, and asks by name only when those hold none:

    Dup.same Dup.A 3 4
    Dup.same Dup.B 8 9

A dump of Lean's core, 98 376 rows, has the same ranges before and after but
one: `Eq.ndrec_symm` had the lines of `Eq`, 46–76, because the name lookup
takes a name ending in `ndrec` for a recursor and asks for its namespace; it
now has its own, 375–377.  Mathlib's rows change when it is dumped again.

## `dt dump` fails on a project that does not import `Lean`

The dump script is Lean code about `Lean.Name`, `Lean.Expr` and `MetaM`, and
its only import is the source's root module.  A Mathlib project brings `Lean`
in through Mathlib; a project of plain Lean does not, and the script does not
compile:

    $ cat Dup.lean
    import Dup.A
    import Dup.B
    $ dt dump project
    …/dump_project.lean:37:7: error(lean.invalidField): Invalid field `isInternalDetail`:
      The environment does not contain `Lean.Name.isInternalDetail`, …
    dt: lake env lean failed for source `project` (exit 1); the script is at …

Twenty-seven errors, none of which says what is missing.  Found while testing
the line-range fix on a two-module project.

Seen with dt 0.45.0, 2026-09-16.

Fixed in 0.46.0.  The script imports `Lean` before the root module, so the
two-module project dumps its three rows.  A core source, whose root is `Lean`,
now imports it twice, which Lean accepts: the dump has the same 98 376 rows.

## `--text` with a constant's name misses the statements that use it

The entry "`--name` AND `--text` reports "no match" where each half matches"
above, again with dt 0.46.0:

    $ dt find --name HasDerivAt --text Finset.sum
    no match: every condition matches on its own; drop one
    $ dt find --name HasDerivAt --uses Finset.sum
    HasDerivAt.pow'  theorem  Mathlib.Analysis.Calculus.Deriv.Pow
    HasDerivAt.sum  theorem  Mathlib.Analysis.Calculus.Deriv.Add
    …

The two halves match different rows.  `--text Finset.sum` alone finds the
docstrings that spell the name out, and a type never does: it prints
`∑ i ∈ u, A i x`.  The name was a constant, and the condition that reads
constants is `--uses`.

Seen with dt 0.46.0, 2026-09-16.

Fixed in 0.47.0.  When a query finds nothing, each dotted `--text` word that
names a constant is searched for as `--uses` instead, and stderr says so:

    $ dt find --name HasDerivAt --text Finset.sum
    dt: --text Finset.sum read as --uses Finset.sum — a type prints a constant as its notation, and only a docstring spells the name
    HasDerivAt.pow'  theorem  Mathlib.Analysis.Calculus.Deriv.Pow
    HasDerivAt.sum  theorem  Mathlib.Analysis.Calculus.Deriv.Add
    …

A text that finds rows as written is left alone, and so is an undotted word
(`exp`, `id`), which a docstring may mean as a word.  This also answers the
older entry: its query was this one, and the ranked union it proposed is not
needed once the text is read as the constant it names.

## A statement edited in place is not reported as stale

Since 0.48.0 a search stays quiet after a rebuild when every declaration of
every recompiled module has a row at the lines the build gives it.  An edit
that keeps the lines passes that check:

    theorem depth_le (f g : Form σ) : (f.le g).depth ≤ max f.depth g.depth := by
    -- edited to
    theorem depth_le (f g : Form σ) : (f.le g).depth = max f.depth g.depth := by

After `lake build` the index still holds `≤`, `dt find` answers from it, and
nothing on stderr says the rows are behind.  The `.ilean` gives the lines of a
declaration and nothing about what it says, so the check needs something that
does: the statement as the source spells it, kept beside the row.

Seen with dt 0.48.0, 2026-09-16.

Fixed in 0.49.0.  `dt index` keeps, beside each row of a source compiled here,
its statement as the source spells it: the declaration's lines up to the
`:=`, `where` or `|` that starts the body, docstring included, whitespace
collapsed (`decl.statement`, schema 4; a schema 3 index gains the column in
place).  A module whose file was saved after its `.olean` gets none.  After a
rebuild the search compares each recompiled declaration's statement in the
source now with the one kept, besides its name and lines.  On a copy of the
transformer project, indexed with 0.49.0 and `Basic.olean` touched each time:

    proof of depth_le edited, same lines         no line
    `= max` changed to `≤ max`, same lines       line printed
    statement changed back                       no line

A statement edited but not yet rebuilt also prints the line once its module
has been rebuilt since the index was written: the index is behind the source
then too.  An index from before 0.49.0 has no statements, so the line prints
after a rebuild until the project is refreshed once.

## A rebuilt module the root does not import is reported as stale

`Transformer/Perspective/Section1_Antipodal.lean` is compiled by `lake build`
but imported by nothing under `Transformer.lean`, so `dt dump` never sees it
and the index has no rows for it.  Since 0.48.0 a search after a rebuild that
recompiled it finds its declarations missing from the index and prints

    dt: `project` was rebuilt since it was indexed; rows may be missing — `dt refresh project`

and `dt refresh project` cannot make that true: the refresh reads the same
root and leaves the module out again.  The line then goes away only because
the refresh moved the index's timestamp past the module's `.olean`.

Seen with dt 0.49.0, 2026-09-16.

Fixed in 0.50.0.  When a rebuilt module declares what the index lacks, the
search now follows `directImports` in the `.ilean` files from the source's
`root` down, and a module that is not reached is left out of the question: no
dump of the root can hold its rows.  A root without an `.ilean` still prints
the line.  An `.olean` whose `.lean` file is gone is read the same way; in
the transformer project that is `Section1_Antipodal`, renamed to
`Section1_IPS`, whose build was left behind.  On a copy of the transformer
project:

    Section1_Antipodal.olean touched     no line (printed with 0.49.0)
    CRASP/Frame.olean touched            line printed

## `dt show` wants the full name of a namespaced declaration, and drops the rest

    dt show "countP_range'_eq_countP" "countP_range'_add" Term.val Term.countSubs

prints only

    dt: countP_range'_eq_countP is not in the index; try `dt find --name countP_range'_eq_countP`

and nothing for the other three names, although `Transformer.CRASP.countP_range'_add`
and the rest are indexed.  Inside `namespace Transformer.CRASP` the short name is
what the source writes, and `dt find --name` finds it at once: `show` could resolve
a unique suffix match (or list the candidates), and go on to the next name after a
miss instead of stopping.

Seen with dt 0.50.0, 2026-09-17.

Fixed in 0.51.0.  A name that is not in the index is read as the end of one:
`dt show` takes the one declaration whose name ends in it, or the one of those
in the project's namespace, and otherwise lists them.  When every name misses,
each miss is printed, not only the first.  With `--import-only`, where the
full name is not printed, stderr says which declaration a name was read as.
On the transformer project:

    dt show "countP_range'_eq_countP" "countP_range'_add" Term.val Term.countSubs
                                   all four shown, 0.18 s
    dt show val                    dt: 90 declarations end in val; name one:
                                   Transformer.CRASP.Term.val, …, and 80 more

## A `lake build` makes the project index stale, and a search then silently misses

After every `lake build` of the transformer project, `dt find --name …` answers
`no match` together with

    dt: `project` was rebuilt since it was indexed; rows may be missing — `dt refresh project`

so a miss cannot be told from a real absence without a refresh (which took
minutes here).  Since the project is rebuilt after nearly every edit, the note is
on almost every search.  `dt find` could refresh only the changed modules on
demand (the `.olean` mtimes are known), or at least search the old rows and say
which modules are stale instead of a blanket "rows may be missing".

Seen with dt 0.51.0, 2026-09-17.

Fixed in 0.52.0. The warning now names the rebuilt modules the root imports —
up to four, then "and N more" — and a rebuild that declares nothing the index
lacks is no longer reported at all. When a `--name` or `--text` search finds no
rows, or a `dt show` name misses, those modules' `.ilean` files and sources are
read and the matching declarations are printed with the statement as the source
spells it, so the answer is usable before a refresh; `dt show` then says the
name is compiled but not indexed instead of absent. A shape or `--uses` search
still gets the warning alone. The incremental refresh is left for a later
version.

## A miss on a rebuilt project cannot read the project

0.52.0 answers a miss from the `.ilean` files of the rebuilt modules, which
gives the name, the module and the statement as the source spells it -- but no
type, no kind, no shape and no dependencies, because nothing has elaborated
them. The rows would say all of that, and measuring what they cost says the
refusal to read them was never justified:

    import Lean + import Transformer, nothing dumped     3.0 s
    one module dumped (19 declarations)                  3.2 s
    the whole project dumped (2578 declarations)         4.3 s
    dt index project --force                             1.0 s
    dt refresh project, end to end                       5.2 s
    the same import on a cold page cache                  24 s

So a project refresh is seconds, and the incremental dump this entry was
written for would save 1.3 s of 5.2 s: the import is the cost, and it is the
same whether one module is dumped or all of them. What is missing is not a
faster refresh but a refresh a search may run at all.

Seen with dt 0.52.0, 2026-09-19.

Fixed in 0.53.0, by refreshing rather than by dumping less. `dt find --refresh`
and `dt show --refresh` read a rebuilt local source again before they answer a
miss, and `refresh_on_miss = true` under `[index]` makes that every search. Off
by default: a search that runs the elaborator without being asked is a search
nobody can time. Local sources only, so a pinned dependency is never dumped
because somebody searched. Everything it says goes to stderr, and a refresh
that fails is reported and swallowed -- the old rows and the 0.52.0 hint both
beat an error. No incremental dump: the measurements above say it would save
1.3 s of 5.2 s.
