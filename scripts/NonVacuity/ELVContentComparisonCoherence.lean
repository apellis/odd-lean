import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
section Content
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
variable (β : Multiset I) (i j : I)
local notation "δ₁" => (β + ([i] : Multiset I))
local notation "δ₂" => ((β + ([i] : Multiset I)) + ([j] : Multiset I))

theorem importing_named_triple_square (l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (hs : δ₁ + ([j,l] : Multiset I) = γ) :
    contentETripleComparison D Sc cutoff N β i j l γ h =
    Functor.associator (contentE D Sc cutoff N β i) (contentE D Sc cutoff N δ₁ j)
      (contentInductionTo D Sc cutoff N δ₂ [l] γ
        (by rw [add_assoc, add_assoc]; exact h)) ≪≫
      Functor.isoWhiskerLeft (contentE D Sc cutoff N β i)
        (contentInductionComp D Sc cutoff N δ₁ [j] [l] γ
          (by rw [add_assoc, add_assoc]; exact h) hs) ≪≫
      contentInductionComp D Sc cutoff N β [i] [j,l] γ hs h :=
  contentETripleComparison_assoc D Sc cutoff N β i j l γ h hs

theorem importing_named_triple_maps (l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (hs : δ₁ + ([j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (t : ContentCategory D Sc cutoff N γ) :
    ((contentETripleComparison D Sc cutoff N β i j l γ h).hom.app M).total t =
    ((Functor.associator (contentE D Sc cutoff N β i) (contentE D Sc cutoff N δ₁ j)
      (contentInductionTo D Sc cutoff N δ₂ [l] γ
        (by rw [add_assoc, add_assoc]; exact h)) ≪≫
      Functor.isoWhiskerLeft (contentE D Sc cutoff N β i)
        (contentInductionComp D Sc cutoff N δ₁ [j] [l] γ
          (by rw [add_assoc, add_assoc]; exact h) hs) ≪≫
      contentInductionComp D Sc cutoff N β [i] [j,l] γ hs h).hom.app M).total t :=
  contentETripleComparison_assoc_total D Sc cutoff N β i j l γ h hs M t
end Content
end OddMath.QuiverHecke.ELVOld

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence
  let some idx := env.header.moduleNames.idxOf? target | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned inventory"
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
#print axioms OddMath.QuiverHecke.ELVOld.importing_named_triple_square
#print axioms OddMath.QuiverHecke.ELVOld.importing_named_triple_maps
