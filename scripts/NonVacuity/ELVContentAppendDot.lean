import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVContentAppendDot

private def D : SKM.Datum Bool (Bool → ℤ) :=
  { CyclotomicAction.AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ =>
      CyclotomicAction.AsymmetricParameters.datum.even_of_odd i j rfl }

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

private def cutoff (_ : Bool) : ℕ := 4
private def ν : List Bool := [false, true]
private def M : Superfunctor ℚ (OldContentCategory D Sc cutoff ν) (SVec ℚ) :=
  (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
    (oldRepresentable D Sc cutoff ⟨ν⟩)

/-- Both moving parities, on a concrete mixed representable, use the whole
selected append-extension comparison and retain arbitrary coefficient arrows. -/
example (i : Bool) (w : OldCategory D Sc cutoff) :=
  oldContentAppendExtensionIso_dot D Sc cutoff ν i M w

example (i : Bool) (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν)) (w : OldCategory D Sc cutoff)
    (h : t.obj ⟶ w) (g : (oldContentAppend D Sc cutoff ν i).obj s ⟶ t) (b : M.obj s) :=
  oldContentAppendExtensionIso_dot_tensor D Sc cutoff ν i M s t w h g b

/-- Input-module naturality retains the dot's original moving parity. -/
example (i : Bool) := oldContentInductionDotComponent_supernatural D Sc cutoff ν i

end NonVacuity.ELVContentAppendDot

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
