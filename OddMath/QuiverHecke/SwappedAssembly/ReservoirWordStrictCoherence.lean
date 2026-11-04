import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
import StringDiagrams.Super.PiTwo

/-! # Structural word comparisons in the strict category of superfunctors

SwappedVacuumCoordinates §§2–7: at zero probe content, the entire path
functor is the unshifted postcomposition functor. This equality records
only the structural associativity and unit comparisons in `PiSCat`.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : Datum I X} {Sc : Scalars D k}
local instance homPi (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

namespace ProbeReservoir
variable (P : ProbeReservoir k (PiSCat.{u,u,u + 1} k) D Sc)

/-- The structural reservoir comparison has equal underlying functors
in the strict category of superfunctors. -/
theorem pathFunctor_eq_homPost_word {l : List (Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0,c) (0,d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    P.pathFunctor p = homPost (k := k) (a := P.T.obj (-P.muP (0,d)))
      (ReservoirWord.word P.W.toRouquierData P.ΛR p hl) := by
  induction l generalizing c with
  | nil =>
    cases p
    rw [ReservoirWord.word_nil]
    rfl
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b,i⟩,r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        rw [pathFunctor_cons, ReservoirWord.word_cons P.W.toRouquierData P.ΛR i r hv p ht]
        have hstep : P.step (true,i) false (0,c) hv =
            homPost (k := k) (P.W.E i (by
              change ReservoirWord.weight D P.ΛR (c - Finsupp.single i 1) + D.α i =
                ReservoirWord.weight D P.ΛR c
              simp only [ReservoirWord.weight, add_assoc]
              rw [contentWeight_sub_single hv])) := by
          simp only [step, homContentPostE, homContentShift, contentParity, map_zero,
            mul_zero, homParityShift_zero, Functor.comp_id]
          rfl
        rw [hstep, ih p ht]
        rfl

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
