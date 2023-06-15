import Lean

class P (n : Nat)

theorem foo (n : Nat) [P n] : True := trivial

-- This should fail, as by default `apply` does not allow synthesis failures.
example : True := by
  apply foo 37

open Lean Meta Elab Tactic Term

/- We copy the `unsafe` term elaborator from `Std` in order to conveniently use `evalTerm`. -/
namespace Std.TermUnsafe

/-- Construct an auxiliary name based on the current declaration name and the given `hint` base. -/
def mkAuxName (hint : Name) : TermElabM Name :=
  withFreshMacroScope do
    let name := (← getDeclName?).getD Name.anonymous ++ hint
    pure $ addMacroScope (← getMainModule) name (← getCurrMacroScope)

elab "unsafe " t:term : term <= expectedType => do
  let mut t ← elabTerm t expectedType
  t ← instantiateMVars t
  if t.hasExprMVar then
    synthesizeSyntheticMVarsNoPostponing
    t ← instantiateMVars t
  if ← logUnassignedUsingErrorInfos (← getMVars t) then throwAbortTerm
  t ← mkAuxDefinitionFor (← mkAuxName `unsafe) t
  let Expr.const unsafeFn unsafeLvls .. := t.getAppFn | unreachable!
  let ConstantInfo.defnInfo unsafeDefn ← getConstInfo unsafeFn | unreachable!
  let implName ← mkAuxName `impl
  addDecl <| Declaration.defnDecl {
    name := implName
    type := unsafeDefn.type
    levelParams := unsafeDefn.levelParams
    value := ← mkOfNonempty unsafeDefn.type
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.safe
  }
  setImplementedBy implName unsafeFn
  pure $ mkAppN (mkConst implName unsafeLvls) t.getAppArgs

end Std.TermUnsafe

/--
`apply (config := cfg) e` is like `apply e` but allows you to provide a configuration
`cfg : ApplyConfig` to pass to the underlying apply operation.
-/
elab (name := applyWith) "apply" " (" &"config" " := " cfg:term ") " e:term : tactic => do
  let cfg ← unsafe evalTerm ApplyConfig (mkConst ``ApplyConfig) cfg
  evalApplyLikeTactic (·.apply · cfg) e

def instP (n : Nat) : P n := {}

example : True := by
  apply (config := { allowSynthFailures := true }) foo
  apply instP
  exact 37

