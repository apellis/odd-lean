import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumWordPairing
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumWordPairingConsumer
open VacuumWordPairing
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem wordHomEquiv_cross_twoExtendedWords (ρ τ : List I) (a b : I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ)
    (hτ : VacuumRepresentable.content (b :: a :: τ) = γ)
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N (b :: a :: τ) γ hτ) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: j :: ρ) (b :: a :: τ) γ heji hτ
      (wordCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji ≫ t) =
    twist k (D.parity i * D.parity j)
      (VacuumRepresentable.wordHomEquiv D Sc cutoff N (j :: i :: ρ) (b :: a :: τ) γ heij hτ t) ≫
      wordCrossArrow D Sc cutoff N ρ β hρ i j γ hij hji heij heji :=
  wordHomEquiv_cross D Sc cutoff N ρ (b :: a :: τ) β hρ i j γ hij hji heij heji hτ t

theorem wordHomEquiv_cross_mixed_twoExtendedWords (ρ τ : List I) (a b : I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ)
    (hτ : VacuumRepresentable.content (b :: a :: τ) = γ)
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N (b :: a :: τ) γ hτ) (hne : i ≠ j) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: j :: ρ) (b :: a :: τ) γ heji hτ
      (wordCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji ≫ t) =
    twist k (D.parity i * D.parity j)
      (VacuumRepresentable.wordHomEquiv D Sc cutoff N (j :: i :: ρ) (b :: a :: τ) γ heij hτ t) ≫
      wordDiagramCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji :=
  wordHomEquiv_cross_mixed D Sc cutoff N ρ (b :: a :: τ) β hρ i j γ hij hji heij heji hτ t hne

theorem wordHomEquiv_cross_equal_twoExtendedWords (ρ τ : List I) (a b : I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i : I) (γ : Multiset I)
    (hij : β + ([i,i] : Multiset I) = γ) (hji : β + ([i,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (i :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: i :: ρ) = γ)
    (hτ : VacuumRepresentable.content (b :: a :: τ) = γ)
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N (i :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N (b :: a :: τ) γ hτ) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: i :: ρ) (b :: a :: τ) γ heji hτ
      (wordCross D Sc cutoff N ρ β hρ i i γ hij hji heij heji ≫ t) =
    -(twist k (D.parity i * D.parity i)
      (VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: i :: ρ) (b :: a :: τ) γ heij hτ t) ≫
      wordDiagramCross D Sc cutoff N ρ β hρ i i γ hij hji heij heji) :=
  wordHomEquiv_cross_equal D Sc cutoff N ρ (b :: a :: τ) β hρ i γ hij hji heij heji hτ t

theorem wordHomEquiv_cross_of_mem_twoExtendedWords (ρ τ : List I) (a b : I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = γ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = γ)
    (hτ : VacuumRepresentable.content (b :: a :: τ) = γ)
    (t : VacuumRepresentable.wordModuleAt D Sc cutoff N (j :: i :: ρ) γ heij ⟶
      VacuumRepresentable.wordModuleAt D Sc cutoff N (b :: a :: τ) γ hτ)
    (q : ZMod 2)
    (ht : VacuumRepresentable.wordHomEquiv D Sc cutoff N (j :: i :: ρ) (b :: a :: τ) γ heij hτ t ∈
      parity (R := k) _ _ q) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (i :: j :: ρ) (b :: a :: τ) γ heji hτ
      (wordCross D Sc cutoff N ρ β hρ i j γ hij hji heij heji ≫ t) =
    sign k ((D.parity i * D.parity j) * q) •
      ((VacuumRepresentable.wordHomEquiv D Sc cutoff N (j :: i :: ρ) (b :: a :: τ) γ heij hτ t) ≫
      wordCrossArrow D Sc cutoff N ρ β hρ i j γ hij hji heij heji) :=
  wordHomEquiv_cross_of_mem D Sc cutoff N ρ (b :: a :: τ) β hρ i j γ hij hji heij heji hτ t q ht

end OddMath.QuiverHecke.ELVOld.VacuumWordPairingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumWordPairing
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing production module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
#print axioms OddMath.QuiverHecke.ELVOld.VacuumWordPairingConsumer.wordHomEquiv_cross_twoExtendedWords
#print axioms OddMath.QuiverHecke.ELVOld.VacuumWordPairingConsumer.wordHomEquiv_cross_mixed_twoExtendedWords
#print axioms OddMath.QuiverHecke.ELVOld.VacuumWordPairingConsumer.wordHomEquiv_cross_equal_twoExtendedWords
#print axioms OddMath.QuiverHecke.ELVOld.VacuumWordPairingConsumer.wordHomEquiv_cross_of_mem_twoExtendedWords
