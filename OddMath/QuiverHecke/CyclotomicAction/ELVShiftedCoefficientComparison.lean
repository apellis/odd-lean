import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionParityComparison

/-! # The prescribed coefficient module and actual parity restriction

The odd shifted Hom coefficient functor is compared with the actual parity
shift of the restriction of the old representable. The comparison is the
identity on underlying quotient coefficients. Its projections and action
agree independently, retaining total exterior parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldCategory_twist (v w : OldCategory D Sc cutoff)
    (p : ZMod 2) (f : v ⟶ w) :
    twist k p f = oldTwist D Sc cutoff p v.word w.word f := by
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
  rw [twist_apply, oldCategory_proj, oldCategory_proj]
  change (ideal D Sc cutoff v.word w.word).mkQ (proj k 0 a) +
    sign k p • (ideal D Sc cutoff v.word w.word).mkQ (proj k 1 a) =
      (ideal D Sc cutoff v.word w.word).mkQ (twist k p a)
  rw [twist_apply, map_add, map_smul]

namespace CyclotomicCrossingTensor

def parityRestrictedRepresentable (i : I) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  (BalancedInduction.restriction (append D Sc cutoff i)).obj
    (supermoduleParityObj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))

theorem coefficientOne_obj_proj (i : I) (v : List I) (s : OldCategory D Sc cutoff)
    (q : ZMod 2) :
    ((coefficient D Sc cutoff 1 i v).obj s).proj q =
      ((parityRestrictedRepresentable D Sc cutoff i v).obj s).proj q := by
  change (shiftedHom D Sc cutoff 1 v (s.word ++ [i])).proj q =
    (SVec.piObj (Supercategory.homSVec k (OldCategory D Sc cutoff)
      (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff i).obj s))).proj q
  rw [SVec.piObj_proj, Supercategory.homSVec_proj, oldCategory_proj]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · apply LinearMap.ext
    intro b
    change b - oldProj D Sc cutoff v (s.word ++ [i]) (1 + 1) b =
      oldProj D Sc cutoff v (s.word ++ [i]) (0 + 1) b
    rw [SVec.zmod2_one_add_one, zero_add]
    have h := proj_add_proj (R := k)
      (X := (⟨v⟩ : OldCategory D Sc cutoff)) (Y := (append D Sc cutoff i).obj s) b
    rw [oldCategory_proj, oldCategory_proj] at h
    exact (eq_sub_of_add_eq ((add_comm _ _).trans h)).symm
  · change oldProj D Sc cutoff v (s.word ++ [i]) (1 + 1) =
      oldProj D Sc cutoff v (s.word ++ [i]) (1 + 1)
    rfl

theorem coefficientOne_map (i : I) (v : List I) {s t : OldCategory D Sc cutoff}
    (f : s ⟶ t) (b : Old D Sc cutoff v (s.word ++ [i])) :
    (coefficient D Sc cutoff 1 i v).map f b =
      (parityRestrictedRepresentable D Sc cutoff i v).map f b := by
  change (oldRepresentableFunctor D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).map
      ((append D Sc cutoff i).map (oldTwist D Sc cutoff 1 s.word t.word f)) b =
    (twist k 1 ((oldRepresentableFunctor D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).map
      ((append D Sc cutoff i).map f))) b
  rw [← oldCategory_twist D Sc cutoff s t 1 f,
    Supercategory.map_twist, Supercategory.map_twist]

/-- The comparison is defined on the actual functors and is identity on every
underlying old quotient coefficient. -/
def coefficientParityIso (i : I) (v : List I) :
    coefficient D Sc cutoff 1 i v ≅
      (parityRestrictedRepresentable D Sc cutoff i v).toFunctor :=
  NatIso.ofComponents (fun s =>
    { hom := LinearMap.id
      inv := LinearMap.id
      hom_inv_id := by ext b; rfl
      inv_hom_id := by ext b; rfl }) (by
        intro s t f
        apply LinearMap.ext
        intro b
        change (coefficient D Sc cutoff 1 i v).map f b =
          (parityRestrictedRepresentable D Sc cutoff i v).map f b
        exact coefficientOne_map D Sc cutoff i v f b)

/-- Objectwise identity is even for the independently defined gradings. -/
theorem coefficientParityIso_hom_mem (i : I) (v : List I) (s : OldCategory D Sc cutoff) :
    (coefficientParityIso D Sc cutoff i v).hom.app s ∈
      parity (R := k) ((coefficient D Sc cutoff 1 i v).obj s)
        ((parityRestrictedRepresentable D Sc cutoff i v).obj s) 0 := by
  intro q
  change LinearMap.id ∘ₗ ((coefficient D Sc cutoff 1 i v).obj s).proj q =
    ((parityRestrictedRepresentable D Sc cutoff i v).obj s).proj (q + 0) ∘ₗ LinearMap.id
  rw [add_zero, LinearMap.id_comp, LinearMap.comp_id]
  exact coefficientOne_obj_proj D Sc cutoff i v s q

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
