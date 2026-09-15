---
name: discrtree
description: Search indexed Lean 4 corpora by the shape of a statement, by name, by the constants a type mentions, or by text, and get the import line that provides a declaration. Use in a Lean project that has a discrtree.toml, or whenever a lemma is easy to describe and hard to name.
---

`dt` answers two questions without a Lean session: where is the declaration
with this shape, and what it takes to use it here. Unlike `#find` it
searches what is not imported.

    dt find 'Real.exp _ ≤ _'        shape: notation, head of each side
    dt find --name exp_le --in Mathlib.Analysis --kind theorem
    dt find --uses Finset.sum --text summable
    dt show <name>...               the declaration, and the import that provides it
    dt deps <name>                  what the proof rests on, level by level
    dt add <name>                   copy it in; dry run unless --write
    dt status                       what is indexed, and whether it is stale
    dt refresh [source]             read it again and re-index

Rules that are not guessable:

- `_` is anything. A pattern implies `--elaborated`: an unelaborated row has
  no conclusion head to match.
- A row marked `[text]` was read by a scanner, not by Lean: no shape, and its
  deps are guesses.
- Lean core (`Init`, `Std`, `Lean`) is a source you add yourself:
  `kind = "core"`, no path, no root. Without it `List.head?` is `no match`.
- `--in` wants a whole module prefix from the root — `Mathlib.Analysis`, not
  `Analysis`. `--name` is a substring, `--text` whole words.
- Conditions are AND; `no match` names the condition to blame. An unknown
  `--source`, or a shape asked of a text source, errors, not an empty result.
- A `dt:` line on stderr means a source moved since it was indexed: rows may
  be missing. Re-run the `dt refresh` it names.
- Default limit is 10. `find --long` adds the full type and the docstring.

`dt <command> --help` has the rest. Setup: `dt init`, edit discrtree.toml,
`dt fetch`, `dt dump` (minutes), `dt index`.
