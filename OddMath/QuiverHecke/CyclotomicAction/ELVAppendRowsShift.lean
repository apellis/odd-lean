/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendRowsEquivalence
/-!
# Moving powers on append common rows

The moving central dot or square translates the last-strand exponent and
leaves every old quotient coefficient unchanged, including exterior coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct DirectSum
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace AppendIdx
variable {i : I} {v w : List I}
def shift (x : AppendIdx i v w) (d : ℕ) : AppendIdx i v w :=
  ⟨(d + x.1.1, x.1.2), x.2⟩
end AppendIdx
namespace ELVOld
theorem appendTail_shift {i : I} {v w : List I} (x : AppendIdx i v w) (d : ℕ) :
    (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ d : End _) ≫ appendTail D Sc x =
      appendTail D Sc (x.shift d) := by
  have hl : x.oldTarget.length = v.length := by simp [AppendIdx.oldTarget]
  rw [dotE_pow, appendTail, cl_comp]
  apply cl_eq_cl
  simp only [AppendIdx.shift, List.replicate_add, List.map_append, List.append_assoc,
    List.map_replicate, hl]

/-- Moving a central power through a common tail works for every old append. -/
theorem centralAppend_pair (i : I) {v t w : List I}
    (h : hom D Sc cutoff (t ++ [i]) w) (b : Old D Sc cutoff v t) :
    centralAppend D Sc cutoff i v w (appendPair D Sc cutoff 0 i h b) =
      appendPair D Sc cutoff 0 i (appendMovingPower D Sc cutoff i t (centralDegree D i) ≫ h) b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  change appendProjection D Sc cutoff i v w
    (appendMovingPower D Sc cutoff i v (centralDegree D i) ≫
      (rightContext D Sc cutoff [i] v t (twist k 0 b) ≫ h)) =
    appendProjection D Sc cutoff i v w
      (rightContext D Sc cutoff [i] v t (twist k 0 b) ≫
        (appendMovingPower D Sc cutoff i t (centralDegree D i) ≫ h))
  rw [← Category.assoc, appendMovingPower_rightContext_cross D Sc cutoff i _ (centralDegree_even D i),
    Category.assoc]

private theorem append_appendMovingPower_tail {i : I} {v w : List I}
    (x : AppendIdx i v w) (d : ℕ) :
    appendMovingPower D Sc cutoff i x.oldTarget d ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc x :
        hom D Sc cutoff (x.oldTarget ++ [i]) w) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc (x.shift d) : hom D Sc cutoff (x.oldTarget ++ [i]) w) := by
  change BoxProd.tmulHom (X := obj D Sc cutoff (x.oldTarget ++ [i]))
    (Y := obj D Sc cutoff (x.oldTarget ++ [i])) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (x.oldTarget ++ [i]))
        (Y := obj D Sc cutoff w) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ = _
  refine (BoxProd.tmulHom_comp_tmulHom
    (X := obj D Sc cutoff (x.oldTarget ++ [i])) (Y := obj D Sc cutoff (x.oldTarget ++ [i]))
    (Z := obj D Sc cutoff w) (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
      SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem)
    (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ d)
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (appendTail_mem D Sc x)).trans ?_
  simp only [koszulSign_zero_left, one_smul]
  change (1 * 1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] _ = _
  rw [one_mul]
  exact congrArg (fun f => (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)
    (appendTail_shift D Sc x d)

/-- The common tail family shifts without changing either its old target or its shuffle. -/
theorem appendCommonTail_shift (i : I) {ν : List I} (q : AppendTailIndex i ν) (m d : ℕ) :
    appendMovingPower D Sc cutoff i q.1.val d ≫ appendCommonTail D Sc cutoff i q m =
      appendCommonTail D Sc cutoff i q (d + m) := by
  have h := append_appendMovingPower_tail D Sc cutoff (appendTailPBW i q m) d
  exact (show ∀ {t t' : List I} (e : t = t')
      (f g : hom D Sc cutoff (t ++ [i]) (appendTailWord i q).val),
      appendMovingPower D Sc cutoff i t d ≫ f = g →
      appendMovingPower D Sc cutoff i t' d ≫ (e ▸ f) = (e ▸ g) from by
        intro t t' e f g hh
        subst t'
        exact hh) (appendTailPBW_oldTarget i q m) _ _ h

/-- Central movement on every coefficient column is the same exponent shift. -/
theorem centralAppend_appendCommonTail (i : I) {ν : List I}
    (q : AppendTailIndex i ν) (m : ℕ) {v : List I} (b : Old D Sc cutoff v q.1.val) :
    centralAppend D Sc cutoff i v (appendTailWord i q).val
      (appendPair D Sc cutoff 0 i (appendCommonTail D Sc cutoff i q m) b) =
    appendPair D Sc cutoff 0 i (appendCommonTail D Sc cutoff i q (centralDegree D i + m)) b := by
  rw [centralAppend_pair, appendCommonTail_shift]

/-- Central movement on one full representable old row. -/
theorem appendContentCentral_tailRow (i : I) (ν : List I)
    (q : AppendTailIndex i ν) (m : ℕ) (b : OldContentRow D Sc cutoff ν q.1.val) :
    appendContentCentral D Sc cutoff i ν (appendTailRow D Sc cutoff i ν q m b) =
      appendTailRow D Sc cutoff i ν q (centralDegree D i + m) b := by
  funext w
  by_cases hw : w = appendTailWord i q
  · subst w
    funext v
    simp only [appendContentCentral, appendRowCentral, OddMath.FiniteHomMatrix.RightModule.map_apply,
      appendCentralNat, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      appendTailRow, LinearMap.single_apply, Pi.single_eq_same, appendPairRow_apply]
    exact centralAppend_appendCommonTail D Sc cutoff i q m (b v)
  · have hzero (n : ℕ) : appendTailRow D Sc cutoff i ν q n b w = 0 := by
      simp [appendTailRow, hw]
    change appendRowCentral D Sc cutoff i ν w.val
      (appendTailRow D Sc cutoff i ν q m b w) = _
    rw [hzero, map_zero, hzero]

/-- Reconstruction intertwines the central moving power and exponent translation. -/
theorem appendRowsReconstruct_shift (i : I) (ν : List I)
    (z : AppendRows D Sc cutoff i ν) :
    appendRowsReconstruct D Sc cutoff i ν
      (appendRowsShift D Sc cutoff i ν (centralDegree D i) z) =
    appendContentCentral D Sc cutoff i ν (appendRowsReconstruct D Sc cutoff i ν z) := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | of q b =>
    change appendRowsReconstruct D Sc cutoff i ν
      (appendRowsShift D Sc cutoff i ν (centralDegree D i)
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) =
      appendContentCentral D Sc cutoff i ν (appendRowsReconstruct D Sc cutoff i ν
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b))
    rw [appendRowsShift, DirectSum.toModule_lof, appendRowsReconstruct_lof,
      appendRowsReconstruct_lof]
    exact (appendContentCentral_tailRow D Sc cutoff i ν q.1 q.2 b).symm

end ELVOld
end OddMath.QuiverHecke
