/-
Copyright (c) 2026 discrtree contributors. Released under the MIT license.

Environment dump for `dt`.

Only the elaborator can read `.olean` and hand back an elaborated type with
notation expanded, so this half of the tool has to be Lean. It writes JSONL and
stops; everything downstream is the Rust binary.

Run it through `dt dump`, which splices the right imports in below and sets the
environment variables this file reads:

  DISCRTREE_OUT      output path for the JSONL (required)
  DISCRTREE_MODULES  comma-separated module prefixes to keep ("" = all)
  DISCRTREE_SOURCE   source name written into every row
  DISCRTREE_DEPS     "0" to skip proof-term dependencies
-/

-- BEGIN IMPORTS (rewritten by `dt dump`)
import Mathlib
-- END IMPORTS

open Lean Meta

namespace Discrtree

/-- Suffixes of compiler-generated declarations that are never worth indexing.
`Name.isInternalDetail` misses most of these. -/
def generatedSuffixes : Array String :=
  #["rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ibelow",
    "ndrec", "ndrecOn", "noConfusion", "noConfusionType", "toCtorIdx",
    "injEq", "inj", "sizeOf_spec", "sizeOf_inst", "ofNat", "match_1",
    "eq_def", "eq_1", "eq_2", "eq_3", "eq_4", "proof_1", "proof_2"]

/-- Whether a declaration is worth a row. -/
def keep (n : Name) : Bool := Id.run do
  if n.isInternalDetail || n.isAnonymous then return false
  -- `Nat.rec`, `Foo.casesOn`, ... : generated, and nobody searches for them.
  if let .str _ s := n then
    if generatedSuffixes.contains s then return false
  -- Macro scopes and hygienic names.
  if n.hasMacroScopes then return false
  return true

/-- Head symbol of an expression: the constant it applies, if any. -/
def headSym (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

/-- The conclusion of a statement, with every binder stripped. Loose bound
variables are fine here: only head symbols are read off the result. -/
partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | .letE _ _ _ b _  => conclusion b
  | .mdata _ b       => conclusion b
  | e                => e

/-- Head symbols of the conclusion's arguments, one level deep. `_` stands for
an argument that is not an application of a constant (a variable, a lambda).
This is the depth-1 half of the shape key; depth 2 is phase 5. -/
def conclArgs (e : Expr) : Array String :=
  e.getAppArgs.map fun a =>
    match headSym a with
    | some n => n.toString
    | none   => "_"

def declKind (env : Environment) (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _  => "axiom"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"
  | .inductInfo _ => if isStructure env ci.name then "structure" else "inductive"
  | .defnInfo _   => "def"

/-- Names a human would never search for, dropped from dependency lists. -/
def keepDep (n : Name) : Bool := keep n

/-- A dependency list: deduplicated, sorted, internals dropped. -/
def depsOf (e : Expr) : Array String :=
  let used := e.getUsedConstants.filter keepDep
  let sorted := used.qsort (·.toString < ·.toString)
  sorted.foldl (init := #[]) fun acc n =>
    let s := n.toString
    if acc.back? == some s then acc else acc.push s

/-- Drop leading and trailing spaces. `String.trim` is deprecated in 4.33 and
its replacement returns a `String.Slice`, so do it here and keep the type. -/
def trimSpaces (s : String) : String :=
  let cs := s.toList.dropWhile (· == ' ')
  String.ofList (cs.reverse.dropWhile (· == ' ')).reverse

def matchesPrefix (prefixes : Array String) (m : Name) : Bool :=
  if prefixes.isEmpty then true
  else
    let s := m.toString
    prefixes.any fun p => s == p || s.startsWith (p ++ ".")

/-- One JSONL row. Field names match `discrtree::model::Decl`. -/
def rowOf (source : String) (withDeps : Bool) (name : Name) (ci : ConstantInfo)
    (module : Name) : MetaM Json := do
  let env ← getEnv
  let ppType ← try (do pure (toString (← ppExpr ci.type))) catch _ => pure ""
  let concl := conclusion ci.type
  let range ← findDeclarationRanges? name
  let doc ← findDocString? env name
  let value? := ci.value? (allowOpaque := true)
  let deps := if withDeps then (value?.map depsOf).getD #[] else #[]
  let hasSorry := ci.type.hasSorry || (value?.map (·.hasSorry)).getD false
  pure <| Json.mkObj [
    ("name",       Json.str name.toString),
    ("source",     Json.str source),
    ("module",     Json.str module.toString),
    ("kind",       Json.str (declKind env ci)),
    ("type",       Json.str ppType),
    ("concl",      match headSym concl with
                   | some n => Json.str n.toString
                   | none   => Json.null),
    ("concl_args", Json.arr ((conclArgs concl).map Json.str)),
    ("consts",     Json.arr ((depsOf ci.type).map Json.str)),
    ("deps",       Json.arr (deps.map Json.str)),
    ("doc",        match doc with
                   | some d => Json.str d
                   | none   => Json.null),
    ("sorry",      Json.bool hasSorry),
    ("line_start", match range with
                   | some r => Json.num r.range.pos.line
                   | none   => Json.null),
    ("line_end",   match range with
                   | some r => Json.num r.range.endPos.line
                   | none   => Json.null),
    ("elaborated", Json.bool true)
  ]

/-- The module a declaration was declared in. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def dumpAll : MetaM Unit := do
  let out ← match (← IO.getEnv "DISCRTREE_OUT") with
    | some p => pure p
    | none   => throwError "DISCRTREE_OUT is not set"
  let source := ((← IO.getEnv "DISCRTREE_SOURCE").getD "unknown")
  let withDeps := ((← IO.getEnv "DISCRTREE_DEPS").getD "1") != "0"
  let prefixes :=
    match (← IO.getEnv "DISCRTREE_MODULES") with
    | some s => (s.splitOn ",").toArray.map trimSpaces |>.filter (!·.isEmpty)
    | none   => #[]
  let env ← getEnv
  -- Imported declarations only: the file being elaborated declares nothing.
  let written ← IO.mkRef 0
  let skipped ← IO.mkRef 0
  let h ← IO.FS.Handle.mk out IO.FS.Mode.write
  env.constants.forM fun name ci => do
    unless keep name do
      return ()
    let some module := moduleOf env name | return ()
    unless matchesPrefix prefixes module do
      return ()
    match ← (try (some <$> rowOf source withDeps name ci module)
              catch _ => pure none) with
    | some row =>
      h.putStrLn row.compress
      let n ← written.modifyGet fun n => (n + 1, n + 1)
      if n % 50000 == 0 then IO.eprintln s!"discrtree: {n} declarations..."
    | none     => skipped.modify (· + 1)
  h.flush
  let w ← written.get
  let s ← skipped.get
  IO.eprintln s!"discrtree: {w} declarations written to {out}\
    {if s == 0 then "" else s!", {s} skipped (elaboration errors)"}"

end Discrtree

#eval Discrtree.dumpAll
