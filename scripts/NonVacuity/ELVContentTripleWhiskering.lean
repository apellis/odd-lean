import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- An importing consumer with swapped suffix endpoints and no inequality assumption. -/
theorem importing_triple_suffix_cross (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (ht : β + ([i,l,j] : Multiset I) = γ)
    (hs : (β + ([i] : Multiset I)) + ([j,l] : Multiset I) = γ)
    (hst : (β + ([i] : Multiset I)) + ([l,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h ht
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
        (contentCrossAffine_mem D Sc j l)) M z =
      ((contentEPairCrossTransform D Sc cutoff N (β + ([i] : Multiset I)) j l γ hs hst).app
        (D.parity j * D.parity l)
        (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M)).total z := by
  rw [contentEPairCross_total]
  exact contentETripleMap_suffix_cross D Sc cutoff N β i j l γ h ht hs hst M z
end OddMath.QuiverHecke.ELVOld

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering
  let some idx := env.header.moduleNames.idxOf? target | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned inventory"
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
#print axioms OddMath.QuiverHecke.ELVOld.importing_triple_suffix_cross
