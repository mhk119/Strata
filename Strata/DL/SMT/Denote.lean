import Lean
import Strata.Languages.Boogie.SMTEncoder

open Strata.SMT
open Classical

def Int.abs (x : Int) : Int :=
  if x < 0 then -x else x

theorem List.getElem_of_findIdx?_eq_some {xs : List α} {p : α → Bool} {i : Nat}
    (h : xs.findIdx? p = some i) : p (xs[i]'((List.findIdx?_eq_some_iff_findIdx_eq.mp h).left)) := by
  sorry

def denoteTermType (ty : TermType) : Option Type :=
  match ty with
  | .prim .bool => Prop
  | .prim .int => Int
  | .prim (.bitvec n) => BitVec n
  | .prim .string => String
  | .option ty => do
    let ty ← denoteTermType ty
    return Option ty
  | _ => none

def denoteTermTypes (as : List TermVar) (out : TermType) : Option Type :=
  match as with
  | []      => denoteTermType out
  | a :: as => do
    let a ← denoteTermType a.ty
    let as ← denoteTermTypes as out
    return a → as

theorem denoteTypeCons_isSome (h : (denoteTermTypes (a :: as) out).isSome) :
    (denoteTermType a.ty).isSome ∧ (denoteTermTypes as out).isSome :=
  sorry

theorem arrow_of_denoteTypeCons_isSome (h : (denoteTermTypes (a :: as) out).isSome) :
    haveI has := denoteTypeCons_isSome h
    (denoteTermTypes (a :: as) out).get h =
    ((denoteTermType a.ty).get has.left → (denoteTermTypes as out).get has.right) :=
  sorry

theorem denoteTypeOut_isSome_of_denoteTypes_isSome (h : (denoteTermTypes as out).isSome) :
    (denoteTermType out).isSome :=
  match as with
  | [] => h
  | a :: as =>
    sorry -- TODO: prove this

structure TermVarDenote where
  id : String
  ty : TermType
  h : (denoteTermType ty).isSome
  var : (denoteTermType ty).get h

abbrev VarEnv := List TermVarDenote

structure VarWF (vs : List TermVar) (Γ : VarEnv) where
  h : vs.length = Γ.length
  ha : ∀ i, (hi : i < vs.length) → vs[i].ty = Γ[i].ty

structure UFDenote where
  id : String
  args : List TermVar
  out : TermType
  h : (denoteTermTypes args out).isSome
  uf : (denoteTermTypes args out).get h

abbrev UFEnv := List UFDenote

structure UFWF (ufs : List UF) (Γ : UFEnv) where
  h : ufs.length = Γ.length
  ha : ∀ i, (hi : i < ufs.length) → ufs[i].args = Γ[i].args ∧ ufs[i].out = Γ[i].out

structure Context where
  ufs : List UF := {}
  vs : List TermVar := {}

structure DenoteEnv (ctx : Context) where
  vΓ : List TermVarDenote
  hv : VarWF ctx.vs vΓ
  ufΓ : List UFDenote
  huf : UFWF ctx.ufs ufΓ

structure DenoteResult (ctx : Context) where
  ty : TermType
  h : (denoteTermType ty).isSome
  res : DenoteEnv ctx → (denoteTermType ty).get h

def checkArgsTyAux (as : List (DenoteResult ctx)) (vs : List TermVar) (hl : as.length = vs.length) : Bool :=
  match as, vs with
  | [], [] => true
  | a :: as, v :: vs =>
    a.ty == v.ty && checkArgsTyAux as vs (Nat.succ.inj hl)
  | _, _ => false

def checkArgsTy (as : List (DenoteResult ctx)) (vs : List TermVar) : Bool :=
  if h : as.length = vs.length then
    checkArgsTyAux as vs h
  else
    false

theorem checkArgsTyAux_true (h : checkArgsTyAux as vs hl) :
  ∀ i, (h : i < as.length) → as[i].ty = (vs[i]'(hl ▸ h)).ty := fun i hi =>
  match as, vs with
  | [], _ => nomatch h
  | a :: as, v :: vs =>
    match i with
    | 0 => eq_of_beq (Bool.and_eq_true_iff.mp h).left
    | i + 1 =>
      (List.getElem_cons_succ a as i hi).symm ▸ (List.getElem_cons_succ v vs i (hl ▸ hi)).symm ▸
      checkArgsTyAux_true (Bool.and_eq_true_iff.mp h).right i (Nat.lt_of_succ_lt_succ hi)

theorem checkArgsTy_true_length (h : checkArgsTy as vs) : as.length = vs.length := by
  unfold checkArgsTy at h
  by_cases hl : as.length = vs.length
  case pos => exact hl
  case neg => rewrite [dif_neg hl] at h; contradiction

theorem checkArgsTy_true_args (h : checkArgsTy as vs) :
  ∀ i, (hi : i < as.length) → as[i].ty = (vs[i]'(checkArgsTy_true_length h ▸ hi)).ty := by
  unfold checkArgsTy at h
  by_cases hl : as.length = vs.length
  case pos => exact checkArgsTyAux_true (dif_pos hl ▸ h)
  case neg =>
    rewrite [dif_neg hl] at h; contradiction

def applyUF (Γ : DenoteEnv ctx) (uf : (denoteTermTypes args out).get h) (as : List (DenoteResult ctx))
    (hl : args.length = as.length) (has : ∀ i, (hi : i < as.length) → as[i].ty = (args[i]'(hl ▸ hi)).ty) :
    (denoteTermType out).get (denoteTypeOut_isSome_of_denoteTypes_isSome h) :=
  match args, as with
  | [], []            => uf
  | arg :: _, a :: as =>
    let uf := arrow_of_denoteTypeCons_isSome h ▸ uf
    haveI ha : denoteTermType arg.ty = denoteTermType a.ty := has 0 (Nat.zero_lt_succ _) ▸ rfl
    let uf := uf (Option.get_congr ha ▸ a.res Γ)
    applyUF Γ uf as (Nat.succ.inj hl) (fun i hi => (has (i + 1) (Nat.succ_lt_succ hi)))

def denoteApplyUF (uf : UF) (as : List (DenoteResult ctx)) : Option (DenoteResult ctx) := do
  if hTys : (denoteTermTypes uf.args uf.out).isSome then
    match h : ctx.ufs.findIdx? (· == uf) with
    | some i =>
      if hufas : checkArgsTy as uf.args then
        haveI hi := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).left
        haveI hiuf := of_decide_eq_true (List.getElem_of_findIdx?_eq_some h)
        let ft (Γ : DenoteEnv ctx) :=
          haveI _ : i < Γ.ufΓ.length := Γ.huf.h ▸ hi
          haveI hufΓ : denoteTermTypes uf.args uf.out = denoteTermTypes Γ.ufΓ[i].args Γ.ufΓ[i].out :=
            hiuf.symm ▸ (Γ.huf.ha i hi).left ▸ (Γ.huf.ha i hi).right ▸ rfl
          @applyUF ctx uf.args uf.out hTys Γ
            (Option.get_congr hufΓ ▸ Γ.ufΓ[i].uf) as (checkArgsTy_true_length hufas).symm (checkArgsTy_true_args hufas)
        return ⟨uf.out, denoteTypeOut_isSome_of_denoteTypes_isSome hTys, ft⟩
      else
        none
    | none => none
  else
    none

mutual

/-
Noncomputable because of `ite` case. Two conditions are needed to make this function computable:
- Disallow quantifiers in the condition of `ite`.
- Return a proof of decidability for each other `Prop`.
-/
noncomputable def denoteTerm (ctx : Context) (t : Term) : Option (DenoteResult ctx) := do
  match t with
  -- Variables and uninterpreted functions (UFs).
  | .var v@hv:{ isBound := true, id := n, ty := ty } =>
    if hTy : (denoteTermType v.ty).isSome then
      match h : ctx.vs.findIdx? (· == v) with
      | some i =>
        haveI hi := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).left
        haveI hiv := of_decide_eq_true (List.getElem_of_findIdx?_eq_some h)
        let ft (Γ : DenoteEnv ctx) :=
          haveI _ : i < Γ.vΓ.length := Γ.hv.h ▸ hi
          haveI hvΓ : denoteTermType v.ty = denoteTermType Γ.vΓ[i].ty := hiv.symm ▸ Γ.hv.ha i hi ▸ rfl
          Option.get_congr hvΓ ▸ Γ.vΓ[i].var
        return ⟨v.ty, hTy, ft⟩
      | none => none
    else
      none
  | .app (.uf uf) as _ =>
    if hTys : (denoteTermTypes uf.args uf.out).isSome then
      match h : ctx.ufs.findIdx? (· == uf) with
      | some i =>
        let as ← denoteTerms ctx as
        if hufas : checkArgsTy as uf.args then
          haveI hi := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).left
          haveI hiuf := of_decide_eq_true (List.getElem_of_findIdx?_eq_some h)
          let ft (Γ : DenoteEnv ctx) :=
            haveI _ : i < Γ.ufΓ.length := Γ.huf.h ▸ hi
            haveI hufΓ : denoteTermTypes uf.args uf.out = denoteTermTypes Γ.ufΓ[i].args Γ.ufΓ[i].out :=
              hiuf.symm ▸ (Γ.huf.ha i hi).left ▸ (Γ.huf.ha i hi).right ▸ rfl
            @applyUF ctx uf.args uf.out hTys Γ
              (Option.get_congr hufΓ ▸ Γ.ufΓ[i].uf) as (checkArgsTy_true_length hufas).symm (checkArgsTy_true_args hufas)
          return ⟨uf.out, denoteTypeOut_isSome_of_denoteTypes_isSome hTys, ft⟩
        else
          none
      | none => none
    else
      none
  -- Quantifiers
  -- TODO (support lists later!)
  | .quant .all [(n, ty)] _ t =>
    if hTy : (denoteTermType ty).isSome then
      let v' := { isBound := true, id := n, ty := ty }
      let vs' := v' :: ctx.vs
      let ctx' := { ufs := ctx.ufs, vs := vs' }
      let ⟨.prim .bool, _, ft⟩ ← denoteTerm ctx' t | none
      let ft (Γ : DenoteEnv ctx) :=
        ∀ x : (denoteTermType ty).get hTy,
          letI var' := { id := n, ty := ty, h := hTy, var := x }
          letI vΓ' := var' :: Γ.vΓ
          haveI hv' : VarWF vs' vΓ' :=
            have h' := show _ + _ = _ + _ from Γ.hv.h ▸ rfl
            have ha' := fun i hivs => match i with
              | 0 => rfl
              | i + 1 =>
                have hivs' := Nat.lt_of_succ_lt_succ hivs
                have hivΓ := Nat.succ_lt_succ (Γ.hv.h ▸ hivs')
                (List.getElem_cons_succ _ ctx.vs i hivs).symm ▸ (List.getElem_cons_succ _ Γ.vΓ i hivΓ).symm ▸ Γ.hv.ha i hivs'
            { h := h', ha := ha' }
          letI Γ' : DenoteEnv ctx' := { ufΓ := Γ.ufΓ, huf := Γ.huf, vΓ := vΓ', hv := hv' }
          ft Γ'
      return ⟨.prim .bool, rfl, ft⟩
    else
      none
  | .quant .exist [(n, ty)] _ t =>
    if hTy : (denoteTermType ty).isSome then
      let v' := { isBound := true, id := n, ty := ty }
      let vs' := v' :: ctx.vs
      let ctx' := { ufs := ctx.ufs, vs := vs' }
      let ⟨.prim .bool, _, ft⟩ ← denoteTerm ctx' t | none
      let ft (Γ : DenoteEnv ctx) :=
        ∃ x : (denoteTermType ty).get hTy,
          letI var' := { id := n, ty := ty, h := hTy, var := x }
          letI vΓ' := var' :: Γ.vΓ
          haveI hv' : VarWF vs' vΓ' :=
            have h' := show _ + _ = _ + _ from Γ.hv.h ▸ rfl
            have ha' := fun i hivs => match i with
              | 0 => rfl
              | i + 1 =>
                have hivs' := Nat.lt_of_succ_lt_succ hivs
                have hivΓ := Nat.succ_lt_succ (Γ.hv.h ▸ hivs')
                (List.getElem_cons_succ _ ctx.vs i hivs).symm ▸ (List.getElem_cons_succ _ Γ.vΓ i hivΓ).symm ▸ Γ.hv.ha i hivs'
            { h := h', ha := ha' }
          letI Γ' : DenoteEnv ctx' := { ufΓ := Γ.ufΓ, huf := Γ.huf, vΓ := vΓ', hv := hv' }
          ft Γ'
      return ⟨.prim .bool, rfl, ft⟩
    else
      none
  -- SMT-Lib core theory
  | .prim (.bool b) =>
    if b = true then return ⟨.prim .bool, rfl, fun _ => True⟩ else return ⟨.prim .bool, rfl, fun _ => False⟩
  | .app .not as _ =>
    let [a] := as | none
    let ⟨.prim .bool, h, a⟩ ← denoteTerm ctx a | none
    return ⟨.prim .bool, h, fun Γ => ¬a Γ⟩
  | .app .and as _ =>
    let [a, b] := as | none
    let ⟨.prim .bool, _, a⟩ ← denoteTerm ctx a | none
    let ⟨.prim .bool, _, b⟩ ← denoteTerm ctx b | none
    return ⟨.prim .bool, rfl, fun Γ => a Γ ∧ b Γ⟩
  | .app .or as _ =>
    let [a, b] := as | none
    let ⟨.prim .bool, _, a⟩ ← denoteTerm ctx a | none
    let ⟨.prim .bool, _, b⟩ ← denoteTerm ctx b | none
    return ⟨.prim .bool, rfl, fun Γ => a Γ ∨ b Γ⟩
  | .app .eq as _ =>
    let [a, b] := as | none
    let ⟨ty₁, _, a⟩ ← denoteTerm ctx a
    let ⟨ty₂, _, b⟩ ← denoteTerm ctx b
    if h₁₂ : ty₁ = ty₂ then
      return ⟨.prim .bool, rfl, fun Γ => a Γ = h₁₂ ▸ b Γ⟩
    else
      none
  | .app .ite as rt =>
    let [c, a, b] := as | none
    let ⟨.prim .bool, _, c⟩ ← denoteTerm ctx c | none
    let ⟨ty₁, h₁, a⟩ ← denoteTerm ctx a
    let ⟨ty₂, _, b⟩ ← denoteTerm ctx b
    if h₁₂ : ty₁ = ty₂ then
      return ⟨ty₁, h₁, fun Γ => if c Γ then a Γ else h₁₂ ▸ b Γ⟩
    else
      none
  | .app .implies as _ =>
    let [a, b] := as | none
    let ⟨.prim .bool, _, a⟩ ← denoteTerm ctx a | none
    let ⟨.prim .bool, _, b⟩ ← denoteTerm ctx b | none
    return ⟨.prim .bool, rfl, fun Γ => a Γ → b Γ⟩
  -- SMT-Lib theory of integers
  | .app .le as _ =>
    let [x, y] := as | none
    let ⟨.prim .int, h₁, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, h₂, y⟩ ← denoteTerm ctx y | none
    return ⟨.prim .bool, rfl, fun Γ => @LE.le Int _ (x Γ) (y Γ)⟩
  | .app .lt as _ =>
    let [x, y] := as | none
    let ⟨.prim .int, h₁, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, h₂, y⟩ ← denoteTerm ctx y | none
    return ⟨.prim .bool, rfl, fun Γ => @LT.lt Int _ (x Γ) (y Γ)⟩
  | .app .ge as _ =>
    let [x, y] := as | none
    let ⟨.prim .int, h₁, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, h₂, y⟩ ← denoteTerm ctx y | none
    return ⟨.prim .bool, rfl, fun Γ => @GE.ge Int _ (x Γ) (y Γ)⟩
  | .app .gt as _ =>
    let [x, y] := as | none
    let ⟨.prim .int, h₁, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, h₂, y⟩ ← denoteTerm ctx y | none
    return ⟨.prim .bool, rfl, fun Γ => @GT.gt Int _ (x Γ) (y Γ)⟩
  | .prim (.int x) =>
    return ⟨.prim .int, rfl, fun _ => x⟩
  | .app .neg as _ =>
    let [x] := as | none
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    return ⟨.prim .int, rfl, fun Γ => @Neg.neg Int _ (x Γ)⟩
  | .app .sub as _ =>
    let [x, y] := as | none
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, _, y⟩ ← denoteTerm ctx y | none
    return ⟨.prim .int, rfl, fun Γ => @HSub.hSub Int Int Int _ (x Γ) (y Γ)⟩
  | .app .add as _ =>
    let [x, y] := as | none
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, _, y⟩ ← denoteTerm ctx y | none
    return ⟨.prim .int, rfl, fun Γ => @HAdd.hAdd Int Int Int _ (x Γ) (y Γ)⟩
  | .app .mul as _ =>
    let [x, y] := as | none
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, _, y⟩ ← denoteTerm ctx y | none
    return ⟨.prim .int, rfl, fun Γ => @HMul.hMul Int Int Int _ (x Γ) (y Γ)⟩
  | .app .div as _ =>
    let [x, y] := as | none
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, _, y⟩ ← denoteTerm ctx y | none
    -- Semantic mismatch with SMT-Lib: `x / 0` is defined as `0` in Lean, but as UF in SMT-Lib.
    return ⟨.prim .int, rfl, fun Γ => @HDiv.hDiv Int Int Int _ (x Γ) (y Γ)⟩
  | .app .mod as _ =>
    let [x, y] := as | none
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    let ⟨.prim .int, _, y⟩ ← denoteTerm ctx y | none
    -- Semantic mismatch with SMT-Lib: `x % 0` is defined as `x` in Lean, but as UF in SMT-Lib.
    return ⟨.prim .int, rfl, fun Γ => @HMod.hMod Int Int Int _ (x Γ) (y Γ)⟩
  | .app .abs as _ =>
    let [x] := as | none
    let ⟨.prim .int, _, x⟩ ← denoteTerm ctx x | none
    return ⟨.prim .int, rfl, fun Γ => (x Γ).abs⟩
  | _ => none

-- Note: Using `List.mapM` breaks definitional equality for some reason, so we use a recursive function instead.
noncomputable def denoteTerms ctx (ts : List Term) : Option (List (DenoteResult ctx)) := do
  match ts with
  | [] => return []
  | a :: as =>
    let a ← denoteTerm ctx a
    let as ← denoteTerms ctx as
    return a :: as

end

noncomputable def denoteBoolTermAux (t : Term) : Option Prop := do
  let some ⟨.prim .bool, _, fi⟩ := denoteTerm {} t | none
  return fi ⟨[], { h := rfl, ha := fun _ hi => nomatch hi }, [], { h := rfl, ha := fun _ hi => nomatch hi }⟩

noncomputable def denoteIntTermAux (t : Term) : Option Int := do
  let some ⟨.prim .int, _, fi⟩ := denoteTerm {} t | none
  return fi ⟨[], { h := rfl, ha := fun _ hi => nomatch hi }, [], { h := rfl, ha := fun _ hi => nomatch hi }⟩

noncomputable def denoteBoolTermFromContext (ctx : Boogie.SMT.Context) (t : Term) : Option Prop := do
  let t := (ctx.axms.foldr (.app .implies [·, ·] (.prim .bool)) t)
  let ⟨.prim .bool, _, fi⟩ ← denoteTerm { ufs := ctx.ufs.toList, vs := ctx.fvs.toList } t | none
  sorry

noncomputable def denoteQuery (ctx : Boogie.SMT.Context) (assums : Array Term) (conc : Term) : Option Prop :=
  denoteBoolTermFromContext ctx (assums.foldr (.app .implies [·, ·] (.prim .bool)) conc)

#reduce denoteIntTermAux (.app .add [(.prim (.int 1)), .prim (.int 2)] (.prim .int))
#reduce (types := true) denoteBoolTermAux (.app .lt [(.prim (.int 1)), .prim (.int 2)] (.prim .int))
-- #reduce (types := true) denoteIntTermAux (.quant .all "a" (.prim .int) (.app .gt [(.prim (.int 42)), .var { isBound := true, id := "a", ty := .prim .int }] (.prim .int)))

example : (denoteBoolTermAux (.quant .all [("a", .prim .int)] (.var { isBound := true, id := "a", ty := .prim .int }) (.app .gt [(.prim (.int 42)), .var { isBound := true, id := "a", ty := .prim .int }] (.prim .int)))) = .some (∀ (x : Int), 42 > x) := by
  rfl
