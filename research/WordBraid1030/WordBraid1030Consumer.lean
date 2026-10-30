import WordBraid1030Checked
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumWordBraid
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
theorem actual_inner_outer_composite (ρ : List I) (β : Multiset I)
    (hρ : VacuumRepresentable.content ρ = β) (i j l : I) (δ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = δ) (hji : β + ([j,i] : Multiset I) = δ)
    (heij : VacuumRepresentable.content (j :: i :: ρ) = δ)
    (heji : VacuumRepresentable.content (i :: j :: ρ) = δ)
    (βi : Multiset I) (hiρ : VacuumRepresentable.content (i :: ρ) = βi)
    (hoij : βi + ([l,j] : Multiset I) = δ + ([l] : Multiset I))
    (hoji : βi + ([j,l] : Multiset I) = δ + ([l] : Multiset I))
    (hoEnd : VacuumRepresentable.content (j :: l :: i :: ρ) = δ + ([l] : Multiset I)) :
    VacuumRepresentable.wordHomEquiv D Sc cutoff N (l :: i :: j :: ρ) (j :: l :: i :: ρ)
      (δ + ([l] : Multiset I)) (congrArg (· + ([l] : Multiset I)) heji) hoEnd
      (((consModuleIso D Sc cutoff N (i :: j :: ρ) δ heji l).inv ≫ (contentInduction D Sc cutoff N δ [l]).map (VacuumWordPairing.wordCross D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫ (consModuleIso D Sc cutoff N (j :: i :: ρ) δ heij l).hom) ≫ (VacuumWordPairing.wordCross D Sc cutoff N (i :: ρ) βi hiρ l j (δ + ([l] : Multiset I)) hoij hoji hoEnd (congrArg (· + ([l] : Multiset I)) heij))) =
    twist k (D.parity i * D.parity j)
      (VacuumRepresentable.wordHomEquiv D Sc cutoff N (l :: j :: i :: ρ) (j :: l :: i :: ρ)
        (δ + ([l] : Multiset I)) (congrArg (· + ([l] : Multiset I)) heij) hoEnd (VacuumWordPairing.wordCross D Sc cutoff N (i :: ρ) βi hiρ l j (δ + ([l] : Multiset I)) hoij hoji hoEnd (congrArg (· + ([l] : Multiset I)) heij))) ≫
      (eqToHom (consObjectEq D Sc cutoff N (j :: i :: ρ) δ heij l).symm ≫ (contentAppend D Sc cutoff N δ [l]).map (VacuumWordPairing.wordCrossArrow D Sc cutoff N ρ β hρ i j δ hij hji heij heji) ≫ eqToHom (consObjectEq D Sc cutoff N (i :: j :: ρ) δ heji l)) :=
  wordHomEquiv_inner_cross_reservoir D Sc cutoff N ρ (j :: l :: i :: ρ) β hρ i j l δ hij hji heij heji hoEnd (VacuumWordPairing.wordCross D Sc cutoff N (i :: ρ) βi hiρ l j (δ + ([l] : Multiset I)) hoij hoji hoEnd (congrArg (· + ([l] : Multiset I)) heij))
end OddMath.QuiverHecke.ELVOld.VacuumWordBraid
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `WordBraid1030Checked
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing scratch module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
#print axioms OddMath.QuiverHecke.ELVOld.VacuumWordBraid.actual_inner_outer_composite
