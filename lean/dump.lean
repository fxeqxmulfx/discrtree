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

/-- What a declaration is, in the words `dt find --kind` takes.

`instance` is an attribute rather than a `ConstantInfo` constructor: every
instance is a `defnInfo`, and reading the constructor alone reports them all as
`def`. That is the kind a reader asks for when the question is whether a type
already has an instance of a class -- so the attribute is read too, and it wins
over `def`, which is how the text scanner has always spelled it. -/
def declKind (env : Environment) (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _  => "axiom"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"
  | .inductInfo _ => if isStructure env ci.name then "structure" else "inductive"
  | .defnInfo _   => if isInstanceCore env ci.name then "instance" else "def"

/-- Names a human would never search for, dropped from dependency lists. -/
def keepDep (n : Name) : Bool := keep n

/-- A dependency list: deduplicated, sorted, internals dropped.

`getUsedConstants` already visits each constant once, so all that is left is
the order. Sorting the names by `toString` rebuilds the string at every
comparison — `k log k` of them per declaration, over three hundred thousand
declarations, twice each. Building every string once and sorting those is the
same answer for `k`. -/
def depsOf (e : Expr) : Array String :=
  let used := e.getUsedConstants.filterMap fun n =>
    if keepDep n then some n.toString else none
  let sorted := used.qsort (· < ·)
  sorted.foldl (init := #[]) fun acc s =>
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

/-- Where `module` declares `name`.

Asked of the module, not of the name. Lean imports a theorem from two modules
when they agree -- Mathlib's `Abelian.CommSq` and `Abelian.Monomorphisms` both
declare the same two instances -- and `findDeclarationRanges?` answers from
whichever module the name was first imported from, so both rows got the lines
of one. The name-keyed lookup is kept for what the module's own entries do not
hold: a range Lean files under another name, or a builtin's. -/
def rangesIn (module : ModuleIdx) (name : Name) : MetaM (Option DeclarationRanges) := do
  let env ← getEnv
  let entries (level : OLeanLevel) :=
    (declRangeExt.getModuleEntries (level := level) env module).binSearch
      (name, default) (fun a b => Name.quickLt a.1 b.1) |>.map (·.2)
  match entries .exported <|> entries .server with
  | some r => pure (some r)
  | none   => findDeclarationRanges? name

/-- One JSONL row. Field names match `discrtree::model::Decl`. -/
def rowOf (source : String) (withDeps : Bool) (name : Name) (ci : ConstantInfo)
    (module : Name) (moduleIdx : ModuleIdx) : MetaM Json := do
  let env ← getEnv
  let ppType ← try (do pure (toString (← ppExpr ci.type))) catch _ => pure ""
  let concl := conclusion ci.type
  let range ← rangesIn moduleIdx name
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

/-- A declaration to write, and the module that declared it, by name and by
index: the index is how the module's own entries are read. -/
structure Work where
  name : Name
  module : Name
  moduleIdx : ModuleIdx
  info : ConstantInfo
  deriving Inhabited

/-- Declarations this dump will write, paired with the module they came from.

Asked of the modules rather than of the constants. The environment is indexed
both ways: `env.constants` is everything the imports brought in -- four hundred
thousand entries once Mathlib is among them -- while `header.moduleData[i]` is
exactly what module `i` declared, and `header.moduleNames[i]` is its name.
Folding over the constants to ask each one which module it came from cost
twenty-two seconds for a project of two thousand declarations, and all but one
second of that was spent deciding that Mathlib was not wanted. Four hundred
module names answer the same question.

Collected up front rather than walked in place: the walk is the only part that
has to be serial, and it is the cheap part. -/
def workList (env : Environment) (prefixes : Array String) :
    Array Work := Id.run do
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut acc := #[]
  for i in [0:names.size] do
    let some m := names[i]? | continue
    if !matchesPrefix prefixes m then continue
    -- A module whose data was not loaded contributes nothing rather than
    -- failing the dump: `moduleData` is as long as `moduleNames` only for the
    -- imports that carry their `.olean` payload.
    let some md := data[i]? | continue
    -- `constNames` exists so that this loop does not have to project the name
    -- out of every `ConstantInfo` to ask `keep` about it.
    for j in [0:md.constNames.size] do
      let some n := md.constNames[j]? | continue
      if !keep n then continue
      let some ci := md.constants[j]? | continue
      acc := acc.push { name := n, module := m, moduleIdx := i, info := ci }
  return acc

/-- Threads to dump on. `DISCRTREE_JOBS` overrides.

The environment is shared and read-only here, so a thread costs its own
elaboration caches and nothing else — which is why this is worth doing in one
process rather than by splitting the library over several, where every one of
them would pay `import Mathlib` again at seven gigabytes. -/
def jobCount : IO Nat := do
  match (← IO.getEnv "DISCRTREE_JOBS").bind String.toNat? with
  | some n => return max n 1
  | none =>
    let hw := (System.Platform.Internal.getHardwareConcurrency ()).toNat
    return if hw == 0 then 4 else hw

/-- Declarations elaborated before the state is thrown away. `ppExpr` fills the
instance and `whnf` caches, and a share of thirty thousand declarations would
otherwise carry every entry to the end. -/
def batchSize : Nat := 2000

/-- One thread's share, written to its own file.

Each thread starts from the same `Core.State`, which holds the environment, and
its result state is dropped: nothing here adds a declaration, so there is
nothing to merge back. -/
def dumpShare (source : String) (withDeps : Bool) (out : String)
    (work : Array Work)
    (ctxCore : Core.Context) (sCore : Core.State) : IO (Nat × Nat) := do
  let h ← IO.FS.Handle.mk out IO.FS.Mode.write
  let mut written := 0
  let mut skipped := 0
  let mut i := 0
  while i < work.size do
    let stop := min (i + batchSize) work.size
    let act : MetaM (Nat × Nat) := do
      let mut w := 0
      let mut s := 0
      for j in [i:stop] do
        let item := work[j]!
        match ← (try (some <$> rowOf source withDeps item.name item.info item.module item.moduleIdx)
                  catch _ => pure none) with
        | some row => h.putStrLn row.compress; w := w + 1
        | none     => s := s + 1
      pure (w, s)
    let ((w, s), _, _) ← act.toIO ctxCore sCore
    written := written + w
    skipped := skipped + s
    i := stop
  h.flush
  IO.eprintln s!"discrtree: {written} declarations into {out}"
  return (written, skipped)

/-- Append `part` to `h` and delete it. Bytes, not lines: the parts are tens of
megabytes and have already been validated on the way out. -/
def appendPart (h : IO.FS.Handle) (part : String) : IO Unit := do
  let hp ← IO.FS.Handle.mk part IO.FS.Mode.read
  let mut buf ← hp.read 1048576
  while !buf.isEmpty do
    h.write buf
    buf ← hp.read 1048576
  IO.FS.removeFile part

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
  let work := workList env prefixes
  let jobs := min (← jobCount) (max work.size 1)
  -- Round robin rather than contiguous blocks. What a declaration costs is the
  -- size of its proof term, and those cluster by file: contiguous shares leave
  -- one thread on `Mathlib.Analysis` long after the rest have finished.
  let shares : Array (Array Work) := Id.run do
    let mut acc := Array.replicate jobs #[]
    for k in [0:work.size] do
      acc := acc.modify (k % jobs) (·.push work[k]!)
    pure acc
  IO.eprintln s!"discrtree: {work.size} declarations on {jobs} threads"
  let ctxCore ← readThe Core.Context
  let sCore ← getThe Core.State
  let mut tasks := #[]
  for i in [0:jobs] do
    tasks := tasks.push (← IO.asTask
      (dumpShare source withDeps s!"{out}.part{i}" shares[i]! ctxCore sCore)
      Task.Priority.dedicated)
  let mut written := 0
  let mut skipped := 0
  for t in tasks do
    match t.get with
    | .ok (w, s) => written := written + w; skipped := skipped + s
    | .error e   => throwError e.toString
  -- Joined in share order, so the dump is one file and the same file however
  -- many threads wrote it.
  let h ← IO.FS.Handle.mk out IO.FS.Mode.write
  for i in [0:jobs] do
    appendPart h s!"{out}.part{i}"
  h.flush
  IO.eprintln s!"discrtree: {written} declarations written to {out}\
    {if skipped == 0 then "" else s!", {skipped} skipped (elaboration errors)"}"

end Discrtree

#eval Discrtree.dumpAll
