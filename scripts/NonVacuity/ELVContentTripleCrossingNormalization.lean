import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem importing_contentWhiskeredPrefixCross_distinct (β : Multiset I) {i j : I} (hij : i ≠ j)
    (l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([j,i,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentETripleMiddleIso D Sc cutoff N β i j l δ γ hδ h hγ).inv.app M).total z ∘ₗ
        ((contentInductionTo D Sc cutoff N δ [l] γ hγ).map
          ((contentEPairCrossTransform D Sc cutoff N β i j δ
            ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ')).app
            (D.parity i * D.parity j) M)).total z ∘ₗ
        ((contentETripleMiddleIso D Sc cutoff N β j i l δ γ hδ' ht hγ).hom.app M).total z =
      contentETripleMap D Sc cutoff N h ht (contentTripleLeft_parity D Sc i j l) M z :=
  contentWhiskeredPrefixCross_distinct D Sc cutoff N β hij l δ γ hδ hδ' h ht hγ M z

theorem importing_contentWhiskeredSuffixCross_distinct (β : Multiset I) (i : I) {j l : I} (hjl : j ≠ l)
    (γ : Multiset I) (h : β + ([i,j,l] : Multiset I) = γ)
    (ht : β + ([i,l,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredSuffixCross D Sc cutoff N β i j l γ h ht M z =
      contentETripleMap D Sc cutoff N h ht (contentTripleRight_parity D Sc i j l) M z :=
  contentWhiskeredSuffixCross_distinct D Sc cutoff N β i hjl γ h ht M z

theorem importing_contentWhiskeredPrefixCross_equal (β : Multiset I) (i l : I)
    (δ γ : Multiset I) (hδ : (β + ([i] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,i,l] : Multiset I) = γ) (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentETripleMiddleIso D Sc cutoff N β i i l δ γ hδ h hγ).inv.app M).total z ∘ₗ
        ((contentInductionTo D Sc cutoff N δ [l] γ hγ).map
          ((contentEPairCrossTransform D Sc cutoff N β i i δ
            ((contentPair_sum β i i).trans hδ) ((contentPair_sum β i i).trans hδ)).app
            (D.parity i * D.parity i) M)).total z ∘ₗ
        ((contentETripleMiddleIso D Sc cutoff N β i i l δ γ hδ h hγ).hom.app M).total z =
      -contentETripleMap D Sc cutoff N h h (contentTripleLeft_parity D Sc i i l) M z :=
  contentWhiskeredPrefixCross_equal D Sc cutoff N β i l δ γ hδ h hγ M z

theorem importing_contentWhiskeredSuffixCross_equal (β : Multiset I) (j i : I)
    (γ : Multiset I) (h : β + ([j,i,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredSuffixCross D Sc cutoff N β j i i γ h h M z =
      -contentETripleMap D Sc cutoff N h h (contentTripleRight_parity D Sc j i i) M z :=
  contentWhiskeredSuffixCross_equal D Sc cutoff N β j i γ h M z
end OddMath.QuiverHecke.ELVOld

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization
  let some idx := env.header.moduleNames.idxOf? target | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned inventory"
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
#print axioms OddMath.QuiverHecke.ELVOld.importing_contentWhiskeredPrefixCross_distinct
#print axioms OddMath.QuiverHecke.ELVOld.importing_contentWhiskeredSuffixCross_distinct
#print axioms OddMath.QuiverHecke.ELVOld.importing_contentWhiskeredPrefixCross_equal
#print axioms OddMath.QuiverHecke.ELVOld.importing_contentWhiskeredSuffixCross_equal
