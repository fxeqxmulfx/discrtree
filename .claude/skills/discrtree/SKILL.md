---
name: discrtree
description: Search indexed Lean 4 corpora by the shape of a statement, by name, by the constants a type mentions, or by text, and get the import line that actually provides a declaration. Use in a Lean project that has a discrtree.toml, or whenever a lemma is easy to describe and hard to name.
---

`dt` answers two questions the repository answers badly: where is the
declaration with this shape, and what does it take to use it here.

    dt find 'Real.exp _ ≤ _'        shape: top-level notation, head of each side
    dt find --name exp_le --in Mathlib.Analysis --kind theorem
    dt find --uses Finset.sum --text summable
    dt show <name>...               the declaration, and the import that provides it
    dt deps <name>                  what the proof rests on, level by level
    dt add <name>                   copy it in; dry run unless --write
    dt status                       what is indexed, and whether it has gone stale

Rules that are not guessable:

- `_` is anything. A pattern implies `--elaborated`, because a row that was
  never elaborated has no conclusion head to match.
- A row marked `[text]` was read by a scanner, not by Lean: no shape, and its
  dependencies are guessed from the file's imports.
- `--in` wants a whole module prefix from the root — `Mathlib.Analysis`, not
  `Analysis`. `--name` is a substring, `--text` is whole words.
- Conditions are AND. `no match` names the condition to blame. An unknown
  `--source`, or a shape asked of a text source, is an error and not an
  empty result.
- Default limit is 10 and the footer says when more matched. `--long` adds the
  full type and the docstring.

`dt <command> --help` has the rest. Setup, once, in order: `dt init` then edit
discrtree.toml, `dt fetch`, `dt dump` (minutes), `dt index`.
