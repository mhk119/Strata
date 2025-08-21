/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean

import Strata.Languages.Boogie.Verifier
import Strata.Languages.C_Simp.Verify
import Strata.DL.Imperative.SMTUtils
import Strata.DL.SMT.CexParser
import Strata.DL.SMT.Translate

open Lean hiding Options

namespace Boogie

def genVCsSingleENV (pE : Program × Env) : MetaM (List MVarId) := do
  let (p, E) := pE
  match E.error with
  | some err =>
    throwError s!"[Strata.Boogie] Error during evaluation!\n\
                  {format err}\n\n\
                  Evaluated program: {p}\n\n"
  | _ =>
    let mut mvs := []
    for obligation in E.deferred do
      let maybeTerms := ProofObligation.toSMTTerms E obligation
      match maybeTerms with
      | .error err =>
        throwError "[Error] SMT Encoding error for obligation {format obligation.label}: \n\
                    {err}\n\n\
                    Evaluated program: {p}\n\n"
      | .ok (terms, ctx) =>
        try
          let mv ← createGoal ctx terms obligation.label
          mvs := mv :: mvs
        catch e =>
           let prog := m!"\n\nEvaluated program:\n{p}"
           throwError "\n\nObligation {obligation.label}: solver error!\
                       \n\nError: {e.toMessageData}\
                       {prog}"
           break
    return mvs

def genVCs (program : Program) (options : Options := Options.default) : MetaM (List MVarId) := do
  match Boogie.typeCheckAndPartialEval options program with
  | .error err =>
    throwError m!"[Strata.Boogie] Type checking error: {err}"
  | .ok pEs =>
    let VCss ← if options.checkOnly then
                 pure []
               else
                 (List.mapM (fun pE => genVCsSingleENV pE) pEs)
    return VCss.flatten.reverse

end Boogie

namespace C_Simp

open C_Simp

def genVCs (program : Strata.C_Simp.Program) (options : Options := Options.default) : MetaM (List MVarId) := do
  let program := Strata.to_boogie program
  Boogie.genVCs program options

end C_Simp

def genVCs (program : Strata.Program) (options : Options := Options.default) : MetaM (List MVarId) := do
  if program.dialect == "Boogie" then
    let (program, errors) := Strata.TransM.run (Strata.translateProgram program)
    let #[] := errors | throwError s!"DDM Transform Error: {errors}"
    trace[strata.verify] f!"AST: {program}"
    Boogie.genVCs program options
  else if program.dialect == "C_Simp" then
    let (program, errors) := Strata.C_Simp.TransM.run (Strata.C_Simp.translateProgram (program.commands))
    let #[] := errors | throwError s!"DDM Transform Error: {errors}"
    trace[strata.verify] f!"AST: {program}"
    C_Simp.genVCs program options
  else
    throwError "Unsupported dialect"

syntax (name := prove_vcs)  "#prove_vcs " ident " by " tacticSeq : command

open Lean.Elab Command in
@[command_elab prove_vcs] unsafe def elabProveVCs : CommandElab := fun stx => do
  match stx with
  | `(#prove_vcs $name:ident by $tacs) => liftTermElabM do
    let type := Expr.const ``Strata.Program []
    let Expr.const c [] ← Term.elabTerm name type | throwError "Expected a constant"
    let env ← evalConst Strata.Program c
    let mvs ← genVCs env { (default : Options) with verbose := false : Options }
    let ts ← mvs.mapM (liftM ∘ MVarId.getType)
    let t :: ts := ts | throwError "Expected at least one VC"
    let (ts, t) := ((t :: ts).dropLast, (t :: ts).getLast?.get rfl)
    let conj := ts.foldr (mkApp2 (.const ``And [])) t
    let hconj ← Meta.mkFreshExprMVar conj (userName := c ++ `vcs)
    let vcs := mvs.map Expr.mvar
    let vc :: vcs := vcs | throwError "Expected at least one VC"
    let (vcs, vc) := ((vc :: vcs).dropLast, (vc :: vcs).getLast?.get rfl)
    let (_, hconjp) := (ts.zip vcs).foldr (init := (t, vc)) fun (t, vc) (ts, vcs) =>
       (mkApp2 (.const ``And []) t ts, mkApp4 (.const ``And.intro []) t ts vc vcs)
    let k := do
      hconj.mvarId!.assign hconjp
      Tactic.replaceMainGoal mvs
      Tactic.evalTactic tacs.raw
      Tactic.pruneSolvedGoals
    let goals ← Tactic.run hconj.mvarId! k
    match goals with
    | [] => return
    | goals => do
      throwErrorAt stx m!"Following goals remain {goals.foldl (init := "") (fun acc g => acc ++ m!"\n  {g}")}"
  | _ => throwUnsupportedSyntax
