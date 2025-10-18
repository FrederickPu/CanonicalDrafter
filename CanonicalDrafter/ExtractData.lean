import Lean
import Lake
import REPL.Lean.InfoTree
import REPL.Frontend
-- example test
-- lake env lean --run ../CanonicalDrafter/ExtractData.lean Mathlib/Combinatorics/Hindman.lean
-- cat .lake/build/ir/Mathlib/Combinatorics/Hindman.ast.json
-- https://github.com/lean-dojo/LeanDojo/issues/247

-- based on https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean from LeanDojo
-- unlike LeanDojo we only care about tracing tactics so we remove commands and premises to reduce storage cost and increase speed.

open Lean

def subscriptToNum (c : Char) : Char :=
  match c with
  | '₀' => '0'
  | '₁' => '1'
  | '₂' => '2'
  | '₃' => '3'
  | '₄' => '4'
  | '₅' => '5'
  | '₆' => '6'
  | '₇' => '7'
  | '₈' => '8'
  | '₉' => '9'
  | _   => c

def increment (s : String) : String :=
  let pre := s.dropRightWhile (fun c => isNumericSubscript c)
  let num := s.takeRightWhile (fun c => isNumericSubscript c)
  pre ++ ((num.map (subscriptToNum)).toNat?.getD 0 + 1).toSubscriptString

partial def disambiguate (s : String) : MetaM String := do
  if ((← getLCtx).findFromUserName? s.toName).isSome then disambiguate (increment s) else return s

def desiredName (userName : Name) (tactic : String) : String :=
  match userName.getRoot with
  | .str _ s => s
  | _ => ((tactic.splitOn).firstM (fun s : String =>
    if !s.isEmpty && isIdFirst (s.get 0) && (s.toSubstring.drop 1).all isIdRest then some s else none
  )).getD "this"

open Lean Elab System

set_option maxHeartbeats 2000000  -- 10x the default maxHeartbeats.


instance : ToJson Substring where
  toJson s := toJson s.toString

instance : ToJson String.Pos where
  toJson n := toJson n.1

deriving instance ToJson for SourceInfo
deriving instance ToJson for Syntax.Preresolved
deriving instance ToJson for Syntax
deriving instance ToJson for Position

/--
The trace of a tactic.
-/
structure TacticTrace where
  goalsBefore: Array String
  goalsAfter: Array String
  pos: String.Pos      -- Start position of the tactic.
  endPos: String.Pos   -- End position of the tactic.
  tactic: String       -- The actual tactic text.
deriving ToJson

inductive Kind
| hypothesis : Kind
| goal : Kind
| original : Kind -- an actual declartion `let, have, obtain`
deriving ToJson

/-
 Given a current goal tactic state string the next relevant sublemmas/hypothesis to be "have drafted"
-/
structure HaveDraft where
  tactic : String
  goal : String
  kind : Kind
  name : String
  type : String
  removals : Array String
  deriving ToJson

/--
The trace of a Lean file.
-/
structure Trace where
  haveDrafts : Array HaveDraft   -- All have drafts in the file
deriving ToJson


abbrev TraceM := StateT Trace TermElabM

namespace Pp

private def addLine (s : String) : String :=
  if s.isEmpty then s else s ++ "\n"

def applyOptions : Options → Options :=
  (pp.proofs.set · false |>
  (pp.motives.all.set · true |>
  (pp.coercions.types.set · true |>
  (pp.unicode.fun.set · true |>
  (pp.funBinderTypes.set · true)))))

open Lean Meta

end Pp

open Lean Meta Elab Tactic

def mkCurriedImplication (hyps : Array LocalDecl) (goal : Expr) : MetaM Expr := do
  -- Extract the `Expr.fvarId` for each hypothesis
  let fvars ← hyps.mapM fun hyp => return mkFVar hyp.fvarId

  -- Use mkForallFVars to abstract the goal over the fvars
  mkForallFVars fvars goal

def extractHypsFromGoal (mvarId : MVarId) : MetaM (Array LocalDecl) := do
  mvarId.withContext do
    pure <| (← getLCtx).foldl (init := #[]) fun acc decl =>
      if decl.isAuxDecl || decl.isImplementationDetail then acc else acc.push decl

open Lean Meta in

def hypsDiff (goalBefore : MVarId) (goalAfter : MVarId) : MetaM (Array LocalDecl × Array LocalDecl) := do
  let beforeDecls ← extractHypsFromGoal goalBefore
  let afterDecls ← extractHypsFromGoal goalAfter
  let beforeFVars := beforeDecls.map (·.fvarId)
  let afterFVars := afterDecls.map (·.fvarId)
  let newHyps := afterDecls.filter fun h => !(beforeFVars.contains h.fvarId)
  let removals := beforeDecls.filter fun h => !(afterFVars.contains h.fvarId)
  return (newHyps, removals)

-- mvar with same type as the goal (but doesn't have the metadata/name)
def goalCopy (goal : MVarId) : MetaM MVarId := do
  return (← goal.withContext do mkFreshExprMVar (← goal.getType)).mvarId!
/-
 returns tuple and Array of (goal, name, type)
-/
def haveDrafts
  (goalsBefore : List MVarId)
  (goalsAfter : List MVarId) (tacticText : String) : MetaM (Array HaveDraft) :=
  let intersection := goalsBefore.filter (fun g => goalsAfter.contains g)
  let goalsBefore := goalsBefore.filter (fun g => !intersection.contains g)
  let goalsAfter := goalsAfter.filter (fun g => !intersection.contains g)
  MonadWithOptions.withOptions Pp.applyOptions do
  match goalsBefore with
  | [gBefore] => do
    if let [gAfter'] := goalsAfter then
      if ← isDefEqGuarded (← gAfter'.getType) (← gBefore.getType) then -- isDefEq used instead of == for mdata
        let (newHyps, removals) ← hypsDiff gBefore gAfter'
        let fvarNewHyps := newHyps.filter (fun h => !h.isLet)
        let letNewHyps := newHyps.filter (fun h => h.isLet)
        if ← gAfter'.withContext do fvarNewHyps.allM (fun h => isProp h.type) then
          let mut goal ← goalCopy gBefore
          let mut result : Array HaveDraft := #[]
          let mut fvars := #[]
          for (h, idx) in fvarNewHyps.zipIdx do
            let goalString := (← Meta.ppGoal goal).pretty.replace "⋯" "sorry"
            let name := ← goal.withContext do disambiguate (desiredName h.userName tacticText)
            let typeString ← gAfter'.withContext do pure ((← ppExpr h.type).pretty.replace "⋯" "sorry")
            let subseq := ((fvarNewHyps.take idx).map (.fvar ·.fvarId))
            let replaced ← gAfter'.withContext do mkCurriedImplication letNewHyps (h.type.replaceFVars subseq fvars)
            let noted := (← goal.note name.toName (← Meta.mkSorry replaced false) (replaced))
            fvars := fvars.push (.fvar noted.1)
            goal := noted.2
            result := result.push {
              tactic := tacticText, name, goal := goalString, type := typeString, kind := Kind.hypothesis, removals := removals.map (·.userName.toString)
            }
          return result

    let mut out : Array HaveDraft := #[]
    let mut goal ← goalCopy gBefore

    -- IO.println s!"{← gBefore.withContext do ppExpr (← gBefore.getType)} num goals after: {goalsAfter.length}"
    for gAfter in goalsAfter do
      let (newHyps, removals) ← hypsDiff gBefore gAfter
      let gAfterName := ((← getMCtx).getDecl gAfter).userName
      let imp ← gAfter.withContext do mkCurriedImplication newHyps (← gAfter.getType)
      let goalString := (← Meta.ppGoal goal).pretty.replace "⋯" "sorry"
      let name := ← goal.withContext do disambiguate (desiredName gAfterName tacticText)
      let typeString := ← gAfter.withContext do return ((← ppExpr imp).pretty.replace "⋯" "sorry")
      out := out.push {
        tactic := tacticText, name, goal := goalString, type := typeString, kind := Kind.goal, removals := removals.map (·.userName.toString)
      }
      goal := (← goal.note name.toName (← goal.withContext do Meta.mkSorry imp false) imp).2
    return out
  | _ => return #[]

namespace Path

/--
Return the path of `path` relative to `parent`.
-/
def relativeTo (path parent : FilePath) : Option FilePath :=
  let rec componentsRelativeTo (pathComps parentComps : List String) : Option FilePath :=
    match pathComps, parentComps with
    | _, [] => mkFilePath pathComps
    | [], _ => none
    | (h₁ :: t₁), (h₂ :: t₂) =>
      if h₁ == h₂ then
        componentsRelativeTo t₁ t₂
      else
        none

    componentsRelativeTo path.components parent.components


/--
Return if the path `path` is relative to `parent`.
-/
def isRelativeTo (path parent : FilePath) : Bool :=
  match relativeTo path parent with
  | some _ => true
  | none => false


/--
Convert the path `path` to an absolute path.
-/
def toAbsolute (path : FilePath) : IO FilePath := do
  if path.isAbsolute then
    pure path
  else
    let cwd ← IO.currentDir
    pure $ cwd / path


private def trim (path : FilePath) : FilePath :=
  assert! path.isRelative
  mkFilePath $ path.components.filter (· != ".")


def packagesDir : FilePath :=
  if Lake.defaultPackagesDir == "packages"  then
    ".lake" / Lake.defaultPackagesDir
  else
    Lake.defaultPackagesDir


def buildDir : FilePath :=
  if Lake.defaultPackagesDir.fileName == "packages" then  -- Lean >= v4.3.0-rc2
    ".lake/build"
  else  -- Lean < v4.3.0-rc2
   "build"


def libDir : FilePath := buildDir / "lib" / "lean"


/--
Convert the path of a *.lean file to its corresponding file (e.g., *.olean) in the "build" directory.
-/
def toBuildDir (subDir : FilePath) (path : FilePath) (ext : String) : Option FilePath :=
  let path' := (trim path).withExtension ext
  match relativeTo path' $ packagesDir / "lean4/src" with
  | some p =>
    match relativeTo p "lean/lake" with
    | some p' => packagesDir / "lean4/lib/lean" / p'
    | none => packagesDir / "lean4/lib" / p
  | none => match relativeTo path' packagesDir with
    | some p =>
      match p.components with
      | [] => none
      | hd :: tl => packagesDir / hd / buildDir / subDir / (mkFilePath tl)
    | none => buildDir / subDir / path'


/--
The reverse of `toBuildDir`.
-/
-- proofwidgets/build/lib/ProofWidgets/Compat.lean
-- proofwidgets/.lake/build/lib
def toSrcDir! (path : FilePath) (ext : String) : FilePath :=
  let path' := (trim path).withExtension ext
  match relativeTo path' $ packagesDir / "lean4/lib" with
  | some p =>  -- E.g., `.lake/packages/lean4/lib/lean/Init/Prelude.olean` -> `.lake/packages/lean4/src/lean/Init/Prelude.lean`
    packagesDir / "lean4/src" / p
  | none =>
    match relativeTo path' packagesDir with
    | some p =>  -- E.g., `.lake/packages/aesop/.lake/build/lib/lean/Aesop.olean`-> `.lake/packages/aesop/Aesop.lean`
      let pkgName := p.components.head!
      let sep := "build/lib/lean/"
      packagesDir / pkgName / (p.toString.splitOn sep |>.tail!.head!)
    | none =>
      -- E.g., `.lake/build/lib/lean/Mathlib/LinearAlgebra/Basic.olean` -> `Mathlib/LinearAlgebra/Basic.lean`
      relativeTo path' libDir |>.get!


/--
Create all parent directories of `p` if they don't exist.
-/
def makeParentDirs (p : FilePath) : IO Unit := do
  let some parent := p.parent | throw $ IO.userError s!"Unable to get the parent of {p}"
  IO.FS.createDirAll parent


/--
Return the *.lean file corresponding to a module name.
-/
def findLean (mod : Name) : IO FilePath := do
  let modStr := mod.toString
  if modStr.startsWith "«lake-packages»." then
    return FilePath.mk (modStr.replace "«lake-packages»" "lake-packages" |>.replace "." "/") |>.withExtension "lean"
  if modStr.startsWith "«.lake»." then
    return FilePath.mk (modStr.replace "«.lake»" ".lake" |>.replace "." "/") |>.withExtension "lean"
  if modStr == "Lake" then
    return packagesDir / "lean4/src/lean/lake/Lake.lean"
  let olean ← findOLean mod
  -- Remove a "build/lib/lean/" substring from the path.
  let lean := olean.toString.replace ".lake/build/lib/lean/" ""
    |>.replace "build/lib/lean/" "" |>.replace "lib/lean/Lake/" "lib/lean/lake/Lake/"
  let mut path := FilePath.mk lean |>.withExtension "lean"
  let leanLib ← getLibDir (← getBuildDir)
  if let some p := relativeTo path leanLib then
    path := packagesDir / "lean4/src/lean" / p
  assert! ← path.pathExists
  return path

end Path


namespace Traversal

partial def getSubNodeGoals (infotree : InfoTree) (rootGoals : List MVarId) (ctx? : Option ContextInfo) : (List MVarId) :=
  match infotree with
  | .context ctx t => getSubNodeGoals t rootGoals (ctx.mergeIntoOuter? ctx?)
  | .node info children =>
    match info with
    | .ofTacticInfo info =>
      if (info.goalsBefore != rootGoals) ∧ info.goalsBefore != [] then
        info.goalsBefore
      else
        (children.map (getSubNodeGoals · rootGoals ctx?)).toList.foldr (· ++ ·) []
    | _                   => []
  | .hole _ => []


def extractTypeExpr (letDeclNode : Syntax) : Option (Option Syntax × Syntax) := do
  -- (Term.haveDecl (Term.haveIdDecl (Term.haveId `y) [] [(Term.typeSpec ":" («term_=_» (num "3") "=" (num "3")))] ":=" `rfl)))
  let letIdDecl := letDeclNode.getArg 0  -- this is the letIdDecl
  -- let lhs := letIdDecl.getArg 0          -- the identifier / pattern (`x` or `⟨a,b⟩`)
  let rhs := letIdDecl.getArg (letIdDecl.getNumArgs - 1)
  let type := match ((letIdDecl.getArg 2).getArg 0).getArg 1 with
    | Syntax.missing => none
    | x => some x

  some (type, rhs)
end Traversal


open Traversal


def getImports (header: TSyntax `Lean.Parser.Module.header) : IO String := do
  -- Similar to `lean --deps` in Lean 3.
  let mut s := ""

  for dep in headerToImports header do
    -- let oleanPath ← findOLean dep.module
    let leanPath ← Path.findLean dep.module
    s := s ++ "\n" ++ leanPath.toString
  return s.trim

/-- Analogue of `findAllInfo` but specialized to tactics. It additionally returns root goals. -/
partial def findAllInfoTactics (t : InfoTree) (ctx? : Option ContextInfo) (rootGoals : List MVarId := []) :
  IO <| List (TacticInfo × Option ContextInfo × List MVarId) := do
  match t with
  | .context ctx t => findAllInfoTactics t (ctx.mergeIntoOuter? ctx?) rootGoals
  | .node info ts =>
    let recursive ← ts.toList.mapM (fun t => findAllInfoTactics t ctx? rootGoals)
    let tInfo ← match info with
    | .ofTacticInfo i =>
      -- IO.println extraGoalsAfter
      if info.isOriginal && i.isSubstantive then
        let rootGoals := if rootGoals.isEmpty then i.goalsBefore else rootGoals
        pure [({ i with goalsAfter := if !i.goalsAfter.isEmpty then i.goalsAfter else (getSubNodeGoals t i.goalsBefore ctx?) }, ctx?, rootGoals)]
      else
        pure []
    | _ => pure []
    pure (tInfo ++ recursive.flatten)
  | _ => pure []

/-- Return all `TacticInfo` nodes in an `InfoTree` with "original" syntax,
each equipped with its relevant `ContextInfo`. -/
def findTacticNodes' (t : InfoTree) : IO (List (TacticInfo × ContextInfo × List MVarId)) := do
  let infos ← findAllInfoTactics t none
  return infos.filterMap fun p => match p with
  | (i, some ctx, rootGoals) => (i, ctx, rootGoals)
  | _ => none

def tacticToHaveDraft (ti : TacticInfo) (ctx : ContextInfo) : MetaM (Array HaveDraft) := do
  let (pb, pa) := stxRange ctx.fileMap ti.stx
  let pb := ctx.fileMap.ofPosition pb
  let pa := ctx.fileMap.ofPosition pa
  -- IO.println ti.stx.formatStx
  let tacticText := ctx.fileMap.source.extract pb pa
  if ["intro", "intros", "rintro", "expose_names"].any (·.isPrefixOf tacticText) then
    return #[]
  else
    let test := match ti.stx with
      | Syntax.node _ `Lean.Parser.Tactic.tacticLet_ args =>
        extractTypeExpr args[1]!
      | Syntax.node _ `Lean.Parser.Tactic.tacticHave_ args =>
        extractTypeExpr args[1]!
      | Syntax.node _ `Lean.Parser.Tactic.obtain args =>
        -- (Tactic.obtain
        --  "obtain"
        --  [(Tactic.rcasesPatMed
        --    [(Tactic.rcasesPat.tuple
        --      "⟨"
        --      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
        --       ","
        --       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `b)]) [])]
        --      "⟩")])]
        --  [":" («term_∧_» («term_=_» (num "2") "=" (num "2")) "∧" («term_=_» (num "3") "=" (num "3")))]
        --  [":=" [(Term.anonymousCtor "⟨" [`rfl "," `rfl] "⟩")]])
        let type : Option Syntax :=
          match (args[2]!.getArg 1) with
          | Syntax.missing => none
          | x => some x
        some ⟨type, (args[args.size - 1]!.getArg 1).getArg 0⟩
      | _ => none
    if let some ⟨type, rhs⟩ := test then ti.goalsBefore[0]!.withContext do
      -- IO.println s!"rhs: {rhs}"
      -- Elaborate rhs to an expression in the meta context (TODO goalBefore.withContext)
      let type ← Lean.Elab.Term.TermElabM.run' (do match type with
        | some type => Term.elabTerm type none
        | none =>
          Meta.inferType (← Term.elabTerm rhs none)) {errToSorry := false}

      -- IO.println s!"type: {← Meta.ppExpr type}"

      let (newHyps, removals) ← hypsDiff ti.goalsBefore[0]! ti.goalsAfter[0]!

      if (← Meta.isProp type) ∧ !(← newHyps.allM (Meta.isProp ·.type)) then
        let draft := (← Meta.ppExpr type).pretty
        let goal := (← Meta.ppGoal (← goalCopy ti.goalsBefore[0]!)).pretty
        return #[({
            tactic := tacticText, name := if let some x := newHyps[0]? then x.userName.toString else "this", goal,
            type := draft, kind := Kind.original, removals := removals.map (·.userName.toString)
        })]
      else
        return ← haveDrafts ti.goalsBefore ti.goalsAfter tacticText
    else
      return ← haveDrafts ti.goalsBefore ti.goalsAfter tacticText

/--
Trace a *.lean file.
-/
unsafe def processFile (path : FilePath) : IO Unit := do
  -- println! path
  let input ← IO.FS.readFile path
  -- Split the processing into two phases to prevent self-reference in proofs in tactic mode
  let (_, _, _, trees) ← IO.processInput input none

  -- for tree in trees do
  --   IO.println (← tree.format)

  let tactics := (← trees.flatMapM (findTacticNodes')).toArray

  let drafts ← tactics.flatMapM (fun ⟨ti, ctx, _⟩ => ctx.runMetaM {} do MonadWithOptions.withOptions Pp.applyOptions do try
    tacticToHaveDraft ti ctx
  catch e =>
    IO.println s!"WARNING: Failed to process tactic {stxRange ctx.fileMap ti.stx}: {← e.toMessageData.format}";
    pure #[])
  let trace := drafts.toJson
  let cwd ← IO.currentDir
  assert! cwd.fileName != "lean4"

  let some relativePath := Path.relativeTo path cwd | throw $ IO.userError s!"Invalid path: {path}"
  let json_path := Path.toBuildDir "ir" relativePath "ast.json" |>.get!
  Path.makeParentDirs json_path
  IO.FS.writeFile json_path trace.pretty

  let dep_path := Path.toBuildDir "ir" relativePath "dep_paths" |>.get!
  Path.makeParentDirs dep_path
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, _, _) ← Parser.parseHeader inputCtx
  IO.FS.writeFile dep_path (← getImports header)


/--
Whether a *.lean file should be traced.
-/
def shouldProcess (path : FilePath) (noDeps : Bool) : IO Bool := do
  if (← path.isDir) ∨ path.extension != "lean" then
    return false

  let cwd ← IO.currentDir
  let some relativePath := Path.relativeTo path cwd |
    throw $ IO.userError s!"Invalid path: {path}"

  if noDeps ∧ Path.isRelativeTo relativePath Path.packagesDir then
    return false

  let some oleanPath := Path.toBuildDir "lib/lean" relativePath "olean" |
    throw $ IO.userError s!"Invalid path: {path}"
  return ← oleanPath.pathExists

/--
Trace all *.lean files in the current directory whose corresponding *.olean file exists,
limiting the number of concurrent tasks to `maxConcurrency`.
-/
def processAllFiles (noDeps : Bool) (maxConcurrency : Nat := 16) : IO Unit := do
  let cwd ← IO.currentDir
  assert! cwd.fileName != "lean4"
  println! "Extracting data at {cwd} with max {maxConcurrency} concurrent processes"

  -- collect all files to process
  let mut filesToProcess := #[]
  for path in ← System.FilePath.walkDir cwd do
    if ← shouldProcess path noDeps then
      filesToProcess := filesToProcess.push path

  let mut idx := 0
  while idx < filesToProcess.size do
    -- take a batch of files up to maxConcurrency
    let batch := filesToProcess.extract idx (Nat.min (idx + maxConcurrency) filesToProcess.size)
    let mut batchTasks : Array (Task (Except IO.Error String) × FilePath) := #[]

    -- launch tasks for this batch
    for path in batch do
      let t ← IO.asTask $ IO.Process.run
        { cmd := "lake", args := #["env", "lean", "--run", "ExtractData.lean", path.toString] }
      batchTasks := batchTasks.push (t, path)

    -- wait for this batch to finish
    for (t, path) in batchTasks do
      match ← IO.wait t with
      | Except.error _ => println! s!"WARNING: Failed to process {path}"
      | Except.ok _    => pure ()

    idx := idx + maxConcurrency



unsafe def main (args : List String) : IO Unit := do
  match args with
  | ["noDeps"] => processAllFiles (noDeps := true)
  | [path] => try processFile (← Path.toAbsolute ⟨path⟩) catch e =>
      println! s!"WARNING: Failed to process {path}: {e}"
  | [] => processAllFiles (noDeps := false)
  | _ => throw $ IO.userError "Invalid arguments"
