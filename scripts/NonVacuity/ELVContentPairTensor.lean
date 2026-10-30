import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairTensor
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
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ₁) (z : ContentCategory D Sc cutoff N δ₂)
    (b : (K).obj w ⟶ z) (a : (J).obj v ⟶ w) (m : M.obj v) :
    ((contentEPairComparison D Sc cutoff N β i j).hom.app M).total z
      (BalancedInduction.tensor K (BalancedInduction.induced J M).toFunctor w b
        (BalancedInduction.tensor J M.toFunctor v a m)) =
    BalancedInduction.tensor A M.toFunctor v
      (eqToHom (congrArg (fun F => F.obj v) e).symm ≫ (K).map a ≫ b) m := by
  apply contentEPairComparison_hom_total_tensor
end Pair
end OddMath.QuiverHecke.ELVOld

#print axioms OddMath.QuiverHecke.ELVOld.contentEPairComparison_hom_total_tensor
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentPairTensor
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
