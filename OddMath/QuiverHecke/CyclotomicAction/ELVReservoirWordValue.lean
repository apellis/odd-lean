import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
import OddMath.QuiverHecke.CyclotomicAction.Global
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierData
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordEvaluation

/-! # Chosen values of the reversed reservoir word

SwappedActionAssembly §6 and SwappedVacuumCoordinates §2: keep the exact
formal-content weight when comparing the surviving reservoir path with
the append-defined chosen E-word value. The word is reversed, while the
original weight group and all strand labels are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ReservoirWordValue
open SwappedAssembly CyclotomicAction
universe u
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Λ : X)

private theorem reversed_word_weight (l : List (SKM.Col I X)) :
    ReservoirWord.weight D Λ (SPath.wordContent l) =
      blockWeight D Λ ((l.map (fun a => a.l.2)).reverse : Multiset I) := by
  induction l with
  | nil => simp [ReservoirWord.weight, SPath.wordContent]
  | cons a l ih =>
    have hs : blockWeight D Λ (((a :: l).map (fun a => a.l.2)).reverse : Multiset I) =
        blockWeight D Λ ((l.map (fun a => a.l.2)).reverse : Multiset I) + D.α a.l.2 := by
      simpa only [List.map_cons, List.reverse_cons, ← Multiset.coe_add,
        Multiset.coe_singleton, add_comm] using
          (blockWeight_cons D Λ a.l.2 ((l.map (fun a => a.l.2)).reverse : Multiset I))
    rw [hs, ← ih]
    simp only [ReservoirWord.weight, SPath.wordContent, map_add, contentWeight,
      Finsupp.weight_single, one_nsmul]
    abel

private theorem path_weight (l : List (SKM.Col I X)) :
    ReservoirWord.weight D Λ (SPath.wordContent l + 0) =
      blockWeight D Λ ((l.map (fun a => a.l.2)).reverse : Multiset I) := by
  simpa only [add_zero] using reversed_word_weight D Λ l

section Modules
variable {k : Type u} [CommRing k] (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

end Modules

section ChosenValue
variable {k : Type u} [CommRing k] [Fintype I]
  (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
local notation "N" => PowerWordContent.powerBound D cutoff L

/-- The actual regular-power empty-word family, at its formal-content weight. -/
def initialValue : ELVWeightProduct D Sc cutoff N Λ (ReservoirWord.weight D Λ 0) :=
  PowerWordWeight.wordFamily D Sc cutoff L Λ (ReservoirWord.weight D Λ 0) []

end ChosenValue

end OddMath.QuiverHecke.ELVOld.ReservoirWordValue
