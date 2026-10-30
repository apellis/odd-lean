import OddMath.QuiverHecke.CyclotomicAction.ELVContentTensorCoherence
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I)
    (γ : Multiset I) (h : δ + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ)
    (z : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N δ τ γ h).obj w ⟶ z)
    (a : (contentAppendTo D Sc cutoff N β σ δ hδ).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ h h').hom.app M).total z
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ τ γ h)
        (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ δ hδ) M).toFunctor w g
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ δ hδ) M.toFunctor v a m)) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h') M.toFunctor v
      (eqToHom (congrArg (fun F => F.obj v)
        (contentAppend_compTo_eq D Sc cutoff N β σ δ hδ τ γ h h')).symm ≫
        (contentAppendTo D Sc cutoff N δ τ γ h).map a ≫ g) m := by
  apply contentInductionCompTo_hom_total_tensor

#print axioms contentInductionCompTo_hom_total_tensor
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentTensorCoherence
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
