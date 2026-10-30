import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairOuterTensor
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

section Pair
variable (β : Multiset I) (i j : I)
local notation "δ₁" => (β + ([i] : Multiset I))
local notation "δ₂" => ((β + ([i] : Multiset I)) + ([j] : Multiset I))
local notation "J" => contentAppend D Sc cutoff N β [i]
local notation "K" => contentAppendTo D Sc cutoff N δ₁ [j] δ₂ rfl
local notation "A" => contentAppendTo D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j)
local notation "e" => contentAppend_comp_eq D Sc cutoff N β [i] [j] δ₂ rfl (contentPair_sum β i j)

example
    (τ : List I) (γ : Multiset I) (hγ : δ₂ + (τ : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ₁) (z : ContentCategory D Sc cutoff N δ₂)
    (t : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).obj z ⟶ t)
    (b : (K).obj w ⟶ z) (a : (J).obj v ⟶ w) (m : M.obj v) :
    ((BalancedInduction.induction (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)).map
      ((contentEPairComparison D Sc cutoff N β i j).hom.app M)).total t
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
        (BalancedInduction.induced K (BalancedInduction.induced J M)).toFunctor z g
        (BalancedInduction.tensor K (BalancedInduction.induced J M).toFunctor w b
          (BalancedInduction.tensor J M.toFunctor v a m))) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
      (BalancedInduction.induced A M).toFunctor z g
      (BalancedInduction.tensor A M.toFunctor v
        (eqToHom (congrArg (fun F => F.obj v) e).symm ≫ (K).map a ≫ b) m) := by
  apply contentEPairComparison_outer_tensor
end Pair
end OddMath.QuiverHecke.ELVOld
#print axioms OddMath.QuiverHecke.ELVOld.contentEPairComparison_outer_tensor
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentPairOuterTensor
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
