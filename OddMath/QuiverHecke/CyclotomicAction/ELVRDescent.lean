/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerBalance
import OddMath.QuiverHecke.CyclotomicAction.ELVQDescent

/-!
# Reverse moving-chain descent over ELV coefficients

Reverse old-ideal descent for the moving chains of Kang–Kashiwara–Oh.
The parity twist acts on the full coefficient-plus-diagram parity. The map
from the prepend-old quotient to the append-old quotient is ground-ring linear;
no inverse, regularity, or injectivity assertion is made.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The reverse moving chain has the same total parity as the forward chain. -/
theorem reverseMoveHom_parity (i : I) (l ν : List I) :
    reverseMoveHom D Sc i l ν ∈ parity (R := k) _ _ (D.parity i * wordSumParity D ν) := by
  have he {A B : (pres D Sc).Presented} (h : A = B) :
      eqToHom h ∈ parity (R := k) A B 0 := by
    subst h
    exact Supercategory.id_mem _
  induction ν generalizing l with
  | nil => simpa only [reverseMoveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero] using he _
  | cons j ν ih =>
    simpa only [reverseMoveHom, wordSumParity, List.map_cons, List.sum_cons, mul_add,
      zero_add, add_zero, mul_comm, add_comm] using Supercategory.comp_mem (he _)
        (Supercategory.comp_mem (ih (l ++ [j]))
          (Supercategory.comp_mem (he _) (Supercategory.comp_mem
            (intertwinerHom_parity D Sc l ν j i) (he _))))

namespace ELVOld
variable (cutoff : I → ℕ)

/-- The reverse affine moving chain with unit ELV coefficient. -/
def reverseMove (i : I) (v : List I) : hom D Sc cutoff (v ++ [i]) (i :: v) :=
  affineUnit D Sc cutoff _ _ (reverseMoveHom D Sc i [] v)

/-- Reverse transport retains the coefficient parity as well as the diagram parity. -/
theorem reverseMove_comp_insert (i : I) {v t : List I} (r : hom D Sc cutoff v t) :
    reverseMove D Sc cutoff i v ≫
        insert D Sc cutoff i v t (twist k (D.parity i * wordSumParity D v) r) =
      rightContext D Sc cutoff [i] v t r ≫ reverseMove D Sc cutoff i t := by
  by_cases hp : wordSumParity D t = wordSumParity D v
  · have hz := reverseMoveHom_parity D Sc i [] t
    rw [hp] at hz
    have h := lift_twisted_square D Sc cutoff
      (affineRightContext D Sc [i] v t) (affineInsert D Sc i v t)
      (reverseMoveHom D Sc i [] v) (reverseMoveHom D Sc i [] t) hz
      (fun hf => MonoidalSupercategory.whiskerLeft_mem (R := k)
        ((pres D Sc).obj (ob D [i])) hf)
      (fun f => by
        simpa only [twist_twist, affineInsert, affineRightContext, LinearMap.coe_mk,
          AddHom.coe_mk, List.nil_append] using
          (hom_comp_reverseMoveHom D Sc i (twist k (D.parity i * wordSumParity D v) f)).symm)
      (twist k (D.parity i * wordSumParity D v) r)
    rw [twist_twist] at h
    change affineUnit D Sc cutoff (v ++ [i]) (i :: v) (reverseMoveHom D Sc i [] v) ≫
        TensorProduct.map LinearMap.id (affineInsert D Sc i v t)
          (twist k (D.parity i * wordSumParity D v) r) =
      TensorProduct.map LinearMap.id (affineRightContext D Sc [i] v t) r ≫
        affineUnit D Sc cutoff (t ++ [i]) (i :: t) (reverseMoveHom D Sc i [] t)
    exact h
  · rw [hom_zero_of_wordParity_ne D Sc cutoff hp r]
    simp only [map_zero, Limits.comp_zero, Limits.zero_comp]

/-- Precomposition with the reverse chain preserves the old relation spans. -/
theorem reverseMove_relations (i : I) {v w : List I}
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    reverseMove D Sc cutoff i v ≫ h ∈ appendRelations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, a, rfl⟩ := hh
    have he := reverseMove_comp_insert D Sc cutoff i
      (twist k (D.parity i * wordSumParity D v) r)
    rw [twist_twist] at he
    rw [← Category.assoc, he, Category.assoc]
    exact Submodule.subset_span ⟨t, _, twist_ideal D Sc cutoff _ hr, _, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c ha

/-- Reverse moving-chain map on the old-only quotients. -/
def rMap (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v w)
    (Linear.leftComp k _ (reverseMove D Sc cutoff i v))
    (fun _ hh => reverseMove_relations D Sc cutoff i hh)

@[simp] theorem rMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w) :
    rMap D Sc cutoff i v w (projection D Sc cutoff i v w h) =
      appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff (v ++ [i]) (i :: v) (reverseMoveHom D Sc i [] v) ≫ h) := rfl

/-- The reverse-after-forward quotient composite is the append-end norm operation. -/
theorem rMap_qMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) :
    rMap D Sc cutoff i v w (qMap D Sc cutoff i v w (appendProjection D Sc cutoff i v w h)) =
      appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff (v ++ [i]) (v ++ [i])
          (reverseMoveHom D Sc i [] v ≫ moveHom D Sc i [] v) ≫ h) := by
  simp only [qMap_projection, rMap_projection, affineUnit_comp, Category.assoc, List.nil_append]

end ELVOld
end OddMath.QuiverHecke
