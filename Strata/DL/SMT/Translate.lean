import Lean
import Strata.Languages.Boogie.SMTEncoder

open Lean
open Strata SMT

structure Translate.State where
  /-- Current de Bruijn level. -/
  level : Nat := 0
  /-- A mapping from variable names to their corresponding type and de Bruijn
      level (not index). So, the variables are indexed from the bottom of the
      stack rather than from the top (i.e., the order in which the symbols are
      introduced in the SMT-LIB file). To compute the de Bruijn index, we
      subtract the variable's level from the current level. -/
  bvars : Std.HashMap Name (Expr × Nat) := {}
deriving Repr

abbrev TranslateM := StateT Translate.State (Except MessageData)

namespace Translate

def findName (n : Name) : TranslateM (Expr × Expr) := do
  let state ← get
  match state.bvars[n]? with
  | some (t, i) => return (t, .bvar (state.level - i - 1))
  | none => throw m!"Error: variable '{n}' not found in context"

private def mkArrow (α β : Expr) : Expr :=
  Lean.mkForall .anonymous BinderInfo.default α β

private def mkProp : Expr :=
  .sort 0

private def mkInt : Expr :=
  .const ``Int []

private def mkBitVec (w : Nat) : Expr :=
  .app (.const ``BitVec []) (mkNatLit w)

private def getBitVecWidth (α : Expr) : TranslateM Nat :=
  match_expr α with
  | BitVec w => match w.nat? with
    | some w => return w
    | none => throw m!"Error: expected natural number for BitVec width, got '{w}'"
  | _ => throw m!"Error: expected BitVec type, got '{α}'"

private def mkString : Expr :=
  .const ``String []

private def mkIntNeg : Expr :=
  mkApp2 (.const ``Neg.neg [0]) mkInt (.const ``Int.instNegInt [])

private def mkIntSub : Expr :=
  mkApp4 (.const ``HSub.hSub [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHSub [0]) mkInt
                 (.const ``Int.instSub []))

private def mkIntAdd : Expr :=
  mkApp4 (.const ``HAdd.hAdd [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHAdd [0]) mkInt
                 (.const ``Int.instAdd []))

private def mkIntMul : Expr :=
  mkApp4 (.const ``HMul.hMul [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHMul [0]) mkInt
                 (.const ``Int.instMul []))

private def mkIntDiv : Expr :=
  mkApp4 (.const ``HDiv.hDiv [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHDiv [0]) mkInt
                 (.const ``Int.instDiv []))

private def mkIntMod : Expr :=
  mkApp4 (.const ``HMod.hMod [0, 0, 0])
         mkInt mkInt mkInt
         (mkApp2 (.const ``instHMod [0]) mkInt
                 (.const ``Int.instMod []))

private def mkIntLE : Expr :=
  mkApp2 (.const ``LE.le [0]) mkInt (.const ``Int.instLEInt [])

private def mkIntLT : Expr :=
  mkApp2 (.const ``LT.lt [0]) mkInt (.const ``Int.instLTInt [])

private def mkIntGE : Expr :=
  mkApp2 (.const ``GE.ge [0]) mkInt (.const ``Int.instLEInt [])

private def mkIntGT : Expr :=
  mkApp2 (.const ``GT.gt [0]) mkInt (.const ``Int.instLTInt [])

private def mkBitVecNeg (w : Nat) : Expr :=
  mkApp2 (.const ``Neg.neg [0])
         (mkBitVec w)
         (.app (.const ``BitVec.instNeg []) (mkNatLit w))

private def mkBitVecSub (w : Nat) : Expr :=
  mkApp4 (.const ``HSub.hSub [0, 0, 0])
         (mkBitVec w) (mkBitVec w) (mkBitVec w)
         (mkApp2 (.const ``instHSub [0]) (mkBitVec w)
                 (.app (.const ``BitVec.instSub []) (mkNatLit w)))

def symbolToName (s : String) : Name :=
  -- Quote the string if a natural translation to Name fails
  if s.toName == .anonymous then
    Name.mkSimple s
  else
    s.toName

def translateSort (ty : TermType) : TranslateM Expr := do
  match ty with
  | .prim .bool =>
    return mkProp
  | .prim .int =>
    return mkInt
  | .prim .real =>
    throw m!"Error: unsupported sort '{repr ty}'"
  | .prim (.bitvec w) =>
    return (mkBitVec w)
  | .prim .string =>
    return mkString
  | .option ty => do
    let ty ← translateSort ty
    return .app (.const ``Option [0]) ty
  | .constr n as =>
    let (_, t) ← findName (symbolToName n)
    let as ← as.mapM translateSort
    return mkAppN t as.toArray

def translateTerm (t : SMT.Term) : TranslateM (Expr × Expr) := do
  match t with
  | .var v =>
    findName (symbolToName v.id)
  | .app (.uf uf) as ty =>
    let (_, f) ← findName (symbolToName uf.id)
    let as ← as.mapM (translateTerm · >>= pure ∘ Prod.snd)
    return (← translateSort ty, mkAppN f as.toArray)
  | .quant q ns _ b =>
    let state ← get
    let translateBinder := fun (n, ty) => do
      let n := symbolToName n
      let ty ← translateSort ty
      modify fun state => { level := state.level + 1, bvars := state.bvars.insert n (ty, state.level) }
      return (n, ty)
    let ns ← ns.mapM translateBinder
    let (_, b) ← translateTerm b
    set state
    let mkQuant := match q with
      | .all => fun (n, ty) e => Expr.forallE n ty e .default
      | .exist => fun (n, ty) e => mkApp2 (.const ``Exists [1]) ty (.lam n ty e .default)
    return (mkProp, ns.foldr mkQuant b)
  | .prim (.bool b) =>
    return (mkProp, .const (if b then ``True else ``False) [])
  | .app .not [a] _ =>
    let (_, a) ← translateTerm a
    return (mkProp, .app (.const ``Not []) a)
  | .app .and as _ =>
    leftAssocOp (.const ``And []) as
  | .app .or as _ =>
    leftAssocOp (.const ``Or []) as
  | .app .eq [x, y] _ =>
    let (α, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp3 (.const ``Eq [1]) α x y)
  | .app .ite [c, x, y] _ =>
    let (_, c) ← translateTerm c
    let (α, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (α, mkApp5 (.const ``ite [1]) α c (.app (.const ``Classical.propDecidable []) c) x y)
  | .app .implies (a :: as) _ =>
    let level := (← get).level
    let (_, a) ← translateTerm a
    let as ← as.mapM fun a => do
      modify fun s => { s with level := s.level + 1 }
      let (_, a) ← translateTerm a
      return a
    modify fun s => { s with level := level }
    let (as, a) := ((a :: as).dropLast, (a :: as).getLast?.get rfl)
    return (mkProp, as.foldr mkArrow a)
  | .prim (.int x) =>
    return (mkProp, toExpr x)
  | .app .neg [a] _ =>
    let (_, a) ← translateTerm a
    return (mkInt, .app mkIntNeg a)
  | .app .sub as _ =>
    leftAssocOp mkIntSub as
  | .app .add as _ =>
    leftAssocOp mkIntAdd as
  | .app .mul as _ =>
    leftAssocOp mkIntMul as
  | .app .div as _ =>
    leftAssocOp mkIntDiv as
  | .app .mod as _ =>
    leftAssocOp mkIntMod as
  -- | .app .abs [a] _ =>
  --   let (_, a) ← translateTerm a
  --   return (mkInt, .app (.const ``Int.abs []) a)
  | .app .le [x, y] _ =>
    let (_, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp2 mkIntLE x y)
  | .app .lt [x, y] _ =>
    let (_, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp2 mkIntLT x y)
  | .app .ge [x, y] _ =>
    let (_, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp2 mkIntGE x y)
  | .app .gt [x, y] _ =>
    let (_, x) ← translateTerm x
    let (_, y) ← translateTerm y
    return (mkProp, mkApp2 mkIntGT x y)
  | t => throw m!"Error: unsupported term '{repr t}'"
where
  leftAssocOp (op : Expr) (as : List SMT.Term) : TranslateM (Expr × Expr) := do
    let a :: as := as | throw m!"Error: expected at least two arguments for '{op}', got '{as.length}'"
    let (α, a) ← translateTerm a
    let as ← as.mapM (translateTerm · >>= pure ∘ Prod.snd)
    return (α, as.foldl (mkApp2 op) a)

def mkTypeArrowN (as : Array SMT.TermType) (a : SMT.TermType) : TranslateM Expr := do
  let level := (← get).level
  let f as a := do
    let a ← translateSort a
    modify fun s => { s with level := s.level + 1 }
    return (as.push a)
  let as ← as.foldlM f #[]
  let a ← translateSort a
  modify fun s => { s with level := level + 1 }
  return as.foldr mkArrow a

def mkPropArrowN (as : Array SMT.Term) (a : SMT.Term) : TranslateM Expr := do
  let level := (← get).level
  let f as a := do
    let (_, a) ← translateTerm a
    modify fun s => { s with level := s.level + 1 }
    return (as.push a)
  let as ← as.foldlM f #[]
  let (_, a) ← translateTerm a
  modify fun s => { s with level := level + 1 }
  return as.foldr mkArrow a

def withTypeDecls (uss : Array Boogie.SMT.Sort) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  let mut decls ← uss.mapM translateTypeDecl
  let (level, bvars) := decls.foldl (fun (lvl, bvs) (n, t) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
  set { bvars, level : Translate.State }
  let b ← k
  set state
  return decls.foldr (fun (n, t) b => .forallE n t b .default) b
where
  translateTypeDecl (us : Boogie.SMT.Sort) : TranslateM (Name × Expr) := do
    return (symbolToName us.name, us.arity.repeatTR (.forallE .anonymous (.sort 1) · .default) (.sort 1))

def withTypeDefs (iss : Map String TermType) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  let defs ← iss.mapM translateTypeDef
  let b ← k
  set state
  -- Note: We set `nondep` to `false` for user-defined types to ensure
  -- type-checking works. Although this could be inefficient, it should be
  -- acceptable since user-defined types are rare.
  return defs.foldr (fun (n, t, v) b => .letE n t v b false) b
where
  translateTypeDef (is : String × TermType) : TranslateM (Name × Expr × Expr) := do
    let state ← get
    let n := symbolToName is.fst
    let t := .sort 1
    let v ← translateSort is.snd
    let bvars := state.bvars.insert n (t, state.level)
    let level := state.level + 1
    set { bvars, level : Translate.State }
    return (n, t, v)

def withFVDecls (fvs : Array TermVar) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  let mut decls ← fvs.mapM translateFVDecl
  let (level, bvars) := decls.foldl (fun (lvl, bvs) (n, t) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
  set { bvars, level : Translate.State }
  let b ← k
  set state
  return decls.foldr (fun (n, t) b => .forallE n t b .default) b
where
  translateFVDecl (fv : TermVar) : TranslateM (Name × Expr) := do
    return (symbolToName fv.id, ← translateSort fv.ty)

def withFunDecls (ufs : Array UF) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  let mut decls ← ufs.mapM translateFunDecl
  let (level, bvars) := decls.foldl (fun (lvl, bvs) (n, t) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
  set { bvars, level : Translate.State }
  let b ← k
  set state
  return decls.foldr (fun (n, t) b => .forallE n t b .default) b
where
  translateFunDecl (uf : UF) : TranslateM (Name × Expr) := do
    let ss := uf.args.map TermVar.ty
    return (symbolToName uf.id, ← mkTypeArrowN ss.toArray uf.out)

def withFunDefs (ifs : Array Boogie.SMT.IF) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  -- it's common for SMT-LIB queries to be "letified" using define-fun to
  -- minimize their size. We don't recurse on each definition to avoid stack
  -- overflows.
  let defs ← ifs.mapM translateFunDef
  let b ← k
  set state
  return defs.foldr (fun (n, t, v) b => .letE n t v b true) b
where
  translateFunDef (f : Boogie.SMT.IF) : TranslateM (Name × Expr × Expr) := do
    let state ← get
    let ps ← f.uf.args.mapM translateParam
    let (level, bvars) := ps.foldl (fun (lvl, bvs) (n, t) => (lvl + 1, bvs.insert n (t, lvl))) (state.level, state.bvars)
    set { bvars, level : Translate.State }
    let s ← translateSort f.uf.out
    let (_, b) ← translateTerm f.body
    let nn := symbolToName f.uf.id
    let t := ps.foldr (fun (n, t) b => .forallE n t b .default) s
    let v := ps.foldr (fun (n, t) b => .lam n t b .default) b
    let bvars := state.bvars.insert nn (t, state.level)
    let level := state.level + 1
    set { bvars, level : Translate.State }
    return (nn, t, v)
  translateParam (v : TermVar) : TranslateM (Name × Expr) := do
    return (symbolToName v.id, ← translateSort v.ty)

def withCtx (ctx : Boogie.SMT.Context) (k : TranslateM Expr) : TranslateM Expr := do
  let state ← get
  let p ← withTypeDecls ctx.sorts <| withTypeDefs ctx.tySubst <| withFVDecls ctx.fvs <|
          withFunDecls ctx.ufs <| withFunDefs ctx.ifs do
    let f as a := do
      let (_, a) ← translateTerm a
      modify fun s => { s with level := s.level + 1 }
      return (as.push a)
    let as ← ctx.axms.foldlM f #[]
    let a ← k
    return as.foldr mkArrow a
  set state
  return p

def translateQuery (ctx : Boogie.SMT.Context) (assums : Array SMT.Term) (conc : SMT.Term) : TranslateM Expr := do
  try
    withCtx ctx do
      mkPropArrowN assums conc
  catch e =>
    throw m!"Error: {e}\nfailed to translate query {repr (← get)}"

end Translate

def translateQuery (ctx : Boogie.SMT.Context) (assums : Array SMT.Term) (conc : SMT.Term) : Except MessageData Expr :=
  (Translate.translateQuery ctx assums conc).run' {}

def createGoal (ctx : Boogie.SMT.Context) (terms : List SMT.Term) (name : String) : MetaM MVarId := do
  let t :: ts := terms | throwError "No terms to discharge!"
  let (ts, t) := ((t :: ts).dropLast, (t :: ts).getLast?.get rfl)
  let t := Factory.not t
  match translateQuery ctx ts.toArray t with
  | .error e =>
    throwError e
  | .ok e =>
    trace[strata.verify] "{e}"
    Meta.check e
    let h ← Meta.mkFreshExprMVar e (userName := Translate.symbolToName name)
    return h.mvarId!

def translateQueryMeta (ctx : Boogie.SMT.Context) (assums : Array SMT.Term) (conc : SMT.Term) : MetaM Expr := do
  Lean.ofExcept (translateQuery ctx assums conc)

open Elab Command in
def elabQuery (ctx : Boogie.SMT.Context) (assums : Array SMT.Term) (conc : SMT.Term) : CommandElabM Unit := do
  runTermElabM fun _ => do
  let e ← translateQueryMeta ctx assums conc
  logInfo e

set_option trace.debug true

/-- info: ∀ (a : Int), 42 > a -/
#guard_msgs in
#eval elabQuery {} #[] (.quant .all [("a", .prim .int)] (.var { isBound := true, id := "a", ty := .prim .int }) (.app .gt [(.prim (.int 42)), .var { isBound := true, id := "a", ty := .prim .int }] (.prim .int)))
