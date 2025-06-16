import Lean
import Std.Data.HashSet.Basic
import Lean.Data.DeclarationRange
import Lean.Data.Json
import Lean.Data.NameMap
import Batteries.Data.NameSet
import Batteries.Data.BinaryHeap
import ImportGraph.RequiredModules

open Lean
structure DefInfo where
  name : Name
  docstring : Option String
  statementUses : NameSet
  proofUses : NameSet
  isThm : Bool
  module : Name
  statementSorry : Bool
  proofSorry : Bool
  pos : Option Position

def isOriginal (s : Name) : Bool :=
  !(s.isInternalDetail || s.isImplementationDetail || s.isInternalOrNum || s.isAnonymous)

-- #eval Submodule.add_mem
def getOriginal (s : Name) : Name :=
  if isOriginal s then
    s
  else
    match s with
    | Name.str p _ => getOriginal p
    | Name.num p _ => getOriginal p
    | Name.anonymous => s

partial def expandUses (range : NameSet) (excluded : NameSet) (env: Environment) (used : Name) (s : Name) (statement : Bool) : NameSet :=
  if isOriginal used then
    NameSet.empty.insert used
  else
    let original := getOriginal used
    /- !isOriginal original : deal with _private.... -/
    if original == s || !isOriginal original then
      let excluded := (excluded.insert s).insert used
      match env.find? used with
      | some info =>
        let usedByUsed := if statement then info.type.getUsedConstantsAsSet else info.getUsedConstantsAsSet
        let expanded := (usedByUsed \ range).union <| NameSet.ofArray <|
          ((usedByUsed ∩ range) \ excluded).toArray.flatMap
          fun x => (expandUses range excluded env x s statement).toArray.append
            <| if statement then (expandUses range excluded env x s false).toArray else #[]
        expanded
      | _ => panic! ""
    else
      NameSet.empty.insert original

def defSort (a b : DefInfo) (mods : Array Name) : Bool :=
  match compare
      #[mods.findIdx (a.module==·), (a.pos.map (·.line)).getD 0]
      #[mods.findIdx (b.module==·), (b.pos.map (·.line)).getD 0]
    with
    | Ordering.lt => true
    | _ => false

def generateFromEnv (env : Environment) (mods : Array Name) : IO (Array DefInfo) := do
  let consts := env.constants
  -- println! (consts.toList.map fun x ↦ x.fst)

  -- refer to https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Listing.20all.20identifiers/near/513859402
  -- to exclude compiler constants like `instMonadOption._cstage1`
  let safeConsts := consts.toList.toArray.filter fun info => !info.snd.isUnsafe

  let ourDefs := safeConsts.filter fun info =>
    match env.getModuleFor? info.fst with
    | some e => e ∈ mods
    | _ => false

  let names := NameSet.ofArray (ourDefs.map fun info => info.fst)
  let _ : MonadEnv IO := {
    getEnv := do pure env,
    modifyEnv := fun _ => do ←panic! ""; pure ()
  }
  let defInfos : Array DefInfo ←
    ourDefs.filterMapM fun info ↦ do
      if ! isOriginal info.fst || ! info.snd.value?.isSome then return none

      let isThm ← match Lean.getOriginalConstKind? env info.fst with
        | some .thm => pure true
        | some .defn => pure false
        | _ => return none

      let proofUses := NameSet.ofArray <|
          (info.snd.getUsedConstantsAsSet ∩ names).toArray.flatMap <|
          fun x => (expandUses names {} env x info.fst false).toArray
      let proofSorry := (proofUses.find? ``sorryAx).isSome || (info.snd.getUsedConstantsAsSet.find? ``sorryAx).isSome
      let statementUses := NameSet.ofArray <|
          (info.snd.type.getUsedConstantsAsSet ∩ names).toArray.flatMap <|
          fun x => (expandUses names {} env x info.fst true).toArray
      let statementSorry := (statementUses.find? ``sorryAx).isSome ||
        (info.snd.type.getUsedConstantsAsSet.find? ``sorryAx).isSome
      let ourStatementUses := statementUses ∩ names
      pure <| some {
        name := info.fst,
        docstring := ← findDocString? env info.fst,
        statementUses := ourStatementUses,
        proofUses := (proofUses ∩ names) \ ourStatementUses,
        isThm := isThm,
        module := (env.getModuleFor? info.fst).get!,
        proofSorry := proofSorry
        statementSorry := statementSorry
        pos := (←Lean.findDeclarationRanges? info.fst).map (fun x => x.range.pos)
      }

  pure (defInfos.heapSort <| fun a b => defSort a b mods)

def infosToJson (defInfos : Array DefInfo) : Json :=
  Json.arr <| defInfos.map <|
    fun d =>
    Json.mkObj [
      ("name", Json.str d.name.toString),
      ("docstring", match d.docstring with | some x => Json.str x | _ => Json.null),
      ("statementUses", Json.arr <| d.statementUses.toArray.map <| fun x => Json.str x.toString),
      ("proofUses", Json.arr <| d.proofUses.toArray.map <| fun x => Json.str x.toString),
      ("isThm", Json.bool d.isThm),
      ("module", Json.str d.module.toString),
      ("proofSorry", Json.bool d.proofSorry),
      ("statementSorry", Json.bool d.statementSorry),
      ("pos", match d.pos with | some p => Json.num p.line | _ => Json.null)
    ]

def main (args : List String) : IO Unit := do
  initSearchPath <| ← findSysroot
  let mods := match args with
    | [] => #[`Groebner.Set, `Groebner.Submodule, `Groebner.Defs, `Groebner.Ideal, `Groebner.Basic]
    | l => l.toArray.map String.toName
  let env ← Lean.importModules (loadExts := false)
    (mods.map fun x ↦ {module:=x, importAll:=false, isExported:=false}) {}
  let infos ← generateFromEnv env <| mods
  let json := infosToJson infos
  IO.FS.writeFile "scripts/defInfos.json" (toString json)
  println! json

-- run_meta do
  -- batteriesLinterExt.getState (← getEnv)
