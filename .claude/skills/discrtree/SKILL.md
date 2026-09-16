---
name: discrtree
description: Search indexed Lean 4 corpora by the shape of a statement, by name, by the constants a type mentions, or by text, and get the import line for a declaration. Use in a Lean project with a discrtree.toml, or whenever a lemma is easy to describe and hard to name.
---

`dt` finds a declaration by the shape of its statement without a Lean
session, and says what it takes to use it. Unlike `#find` it reaches what is
not imported.

    dt find 'Real.exp _ ≤ _'        shape: notation, head of each side
    dt find --name exp_le --in Mathlib.Analysis --kind theorem
    dt find --uses Finset.sum --text summable
    dt show <name>...               the declaration, and the import for it
    dt deps <name>                  what the proof rests on, level by level
    dt add <name>                   copy it in; dry run unless --write
    dt status                       what is indexed, and whether it is stale
    dt refresh [source]             read it again and re-index

Not guessable:

- Write a pattern as Lean prints it: `_` is anything, and so are a one-letter
  name (`a`, `x`) and a lambda; `A → B` searches for `B` with the hypotheses
  as `--uses`. A pattern implies `--elaborated`: a text row has no shape.
- A row marked `[text]` was read by a scanner, not Lean: no shape, guessed deps.
- Lean core (`Init`, `Std`, `Lean`) is a source you add yourself:
  `kind = "core"`, no path or root. Without it `List.head?` is `no match`.
- `--in` wants a whole module prefix from the root: `Mathlib.Analysis`, not
  `Analysis`. `--name` is a substring; `--text` is whole words, and repeats.
- Conditions are AND; `no match` says which one to blame.
- A `dt:` line on stderr means the index is behind the source and rows may be
  missing; re-run the `dt refresh` it names.
- Default limit 10. `find --long` adds the type and docstring; `show` prints
  the whole declaration, source and all.

`dt <command> --help` has the rest. Setup: `dt init`, edit discrtree.toml,
`dt fetch`, `dt dump` (minutes), `dt index`.
