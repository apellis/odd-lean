/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQPRepeated
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPEquation

/-!
# Repeated-odd QP recursion over ELV coefficients

The repeated-odd step of `DeformedGlobalQP.md` §3. The two prefix signs
cancel after square-difference cancellation and odd source-difference preservation
in the old-only quotient. No moving cyclotomic relation is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem dot_whisker (i : I) (v : List I) :
    dotE D Sc [i] 0 ▷ (pres D Sc).obj (ob D v) = dotE D Sc (i :: v) 0 := by
  rw [dotE_whiskerRight D Sc [i] v 0 (by simp)]
  rfl

private theorem odd_induction_hom {v w : List I} {P : hom D Sc cutoff v w → Prop}
    (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

private theorem movingPower_one (i : I) (v : List I) :
    movingPower D Sc cutoff i v 1 =
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] dotE D Sc (i :: v) 0 := by
  exact congrArg (fun f : End ((pres D Sc).obj (ob D (i :: v))) =>
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)
    (pow_one (dotE D Sc (i :: v) 0))

/-- The moving dot twists the total coefficient-plus-diagram parity of an old Hom. -/
theorem movingDot_insert (i : I) {v t : List I} (r : hom D Sc cutoff v t) :
    movingPower D Sc cutoff i v 1 ≫ insert D Sc cutoff i v t r =
      insert D Sc cutoff i v t (twist k (D.parity i) r) ≫
        movingPower D Sc cutoff i t 1 := by
  induction r using odd_induction_hom D Sc cutoff with
  | zero => simp only [map_zero, Limits.comp_zero, Limits.zero_comp]
  | add r s hr hs => simp only [map_add, Preadditive.comp_add, Preadditive.add_comp, hr, hs]
  | tmul p q a f ha hf =>
    change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff at a
    have hx : dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) :=
      positionedDot_parity D Sc [] [] i
    have hxt : dotE D Sc (i :: t) 0 ∈ parity (R := k) _ _ (D.parity i) :=
      positionedDot_parity D Sc [] t i
    have ht : (a ⊗ₜ[k] f : hom D Sc cutoff v t) ∈
        parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff t) (p + q) :=
      BoxProd.tmul_mem_parity (X := obj D Sc cutoff v) (Y := obj D Sc cutoff t) ha hf
    change movingPower D Sc cutoff i v 1 ≫ insert D Sc cutoff i v t (a ⊗ₜ[k] f) =
      insert D Sc cutoff i v t (twist k (D.parity i) (a ⊗ₜ[k] f)) ≫ movingPower D Sc cutoff i t 1
    rw [twist_of_mem _ ht]
    change movingPower D Sc cutoff i v 1 ≫ insert D Sc cutoff i v t (a ⊗ₜ[k] f) =
      insert D Sc cutoff i v t (sign k (D.parity i * (p + q)) •
        (a ⊗ₜ[k] f : hom D Sc cutoff v t)) ≫ movingPower D Sc cutoff i t 1
    erw [map_smul]
    rw [Linear.smul_comp]
    rw [movingPower_one, movingPower_one]
    change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
        (Y := obj D Sc cutoff (i :: v)) (SuperalgebraCat.ofElem 1) (dotE D Sc (i :: v) 0) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (i :: t)) a (affineInsert D Sc i v t f) =
      sign k (D.parity i * (p + q)) •
        (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (i :: t)) a (affineInsert D Sc i v t f) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: t))
          (Y := obj D Sc cutoff (i :: t)) (SuperalgebraCat.ofElem 1) (dotE D Sc (i :: t) 0))
    erw [BoxProd.tmulHom_comp_tmulHom
      (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: v))
      (Z := obj D Sc cutoff (i :: t))
      (show (SuperalgebraCat.ofElem (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ∈
        parity (R := k) (obj D Sc cutoff (i :: v)).fst _ 0 from id_mem (R := k) _) _ _
      (MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D [i])) hf),
      BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: t))
        (Z := obj D Sc cutoff (i :: t)) ha _ _ hxt]
    have hn : dotE D Sc (i :: v) 0 ≫ affineInsert D Sc i v t f =
        koszulSign (D.parity i) q •
          (affineInsert D Sc i v t f ≫ dotE D Sc (i :: t) 0) := by
      rw [← dot_whisker D Sc i v, ← dot_whisker D Sc i t]
      exact MonoidalSupercategory.super_interchange hx hf
    change koszulSign 0 q • ((a * 1) ⊗ₜ[k]
      (dotE D Sc (i :: v) 0 ≫ affineInsert D Sc i v t f)) =
      sign k (D.parity i * (p + q)) • (koszulSign p (D.parity i) • ((1 * a) ⊗ₜ[k]
        (affineInsert D Sc i v t f ≫ dotE D Sc (i :: t) 0)))
    rw [hn]
    simp only [mul_one, one_mul, TensorProduct.tmul_smul, koszulSign_smul (R := k),
      zero_mul, sign_zero, smul_smul, ← sign_add, mul_add, mul_comm p, add_comm]
    rw [((by decide : ∀ a b : ZMod 2, a + (a + b) = b) _ _)]

/-- Precomposition by the moving odd dot preserves the defining old relations. -/
theorem movingDot_relations (i : I) {v w : List I} {h : hom D Sc cutoff (i :: v) w}
    (hh : h ∈ relations D Sc cutoff i v w) :
    movingPower D Sc cutoff i v 1 ≫ h ∈ relations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, movingDot_insert, Category.assoc]
    exact Submodule.subset_span ⟨t, _, twist_ideal D Sc cutoff _ hr, _, rfl⟩
  | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

/-- Unlike cancellation, preservation holds for the unsquared moving dot. -/
theorem projection_source_difference_zero (i : I) (v z : List I) (a : ℕ)
    (h : hom D Sc cutoff (i :: v) z) (hh : projection D Sc cutoff i v z h = 0) :
    projection D Sc cutoff i v z
      ((sourceDotPower D Sc cutoff (i :: v) (a + 1) 1 -
        sourceDotPower D Sc cutoff (i :: v) 0 1) ≫ h) = 0 := by
  have ho := congrArg (oldSourceTarget D Sc cutoff i v z (sourceDotPower D Sc cutoff v a 1)) hh
  rw [map_zero] at ho
  change projection D Sc cutoff i v z
    (insert D Sc cutoff i v v (sourceDotPower D Sc cutoff v a 1) ≫ h) = 0 at ho
  rw [insert_sourceDotPower] at ho
  have hm : projection D Sc cutoff i v z (movingPower D Sc cutoff i v 1 ≫ h) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero (relations D Sc cutoff i v z)).mpr
    exact movingDot_relations D Sc cutoff i
      ((Submodule.Quotient.mk_eq_zero (relations D Sc cutoff i v z)).mp hh)
  rw [Preadditive.sub_comp, map_sub, ho]
  exact sub_eq_zero.mpr hm.symm

/-- Cancel a positive even-parity source power against an arbitrary old positioned power. -/
theorem projection_power_difference_cancel (i : I) (v z : List I) (a d : ℕ)
    (hd : d • D.parity i = 0) (hpos : 0 < d) (h : hom D Sc cutoff (i :: v) z)
    (hh : projection D Sc cutoff i v z
      ((sourceDotPower D Sc cutoff (i :: v) (a + 1) d -
        sourceDotPower D Sc cutoff (i :: v) 0 d) ≫ h) = 0) :
    projection D Sc cutoff i v z h = 0 := by
  apply movingPower_eq_oldSource D Sc cutoff 0 i v z d hd hpos
    (sourceDotPower D Sc cutoff v a d)
  change projection D Sc cutoff i v z (movingPower D Sc cutoff i v d ≫ h) =
    projection D Sc cutoff i v z (insert D Sc cutoff i v v (sourceDotPower D Sc cutoff v a d) ≫ h)
  rw [insert_sourceDotPower]
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hh
  exact hh.symm

private theorem rightContext_affineUnit_dotPower (i : I) (μ σ : List I) (b d : ℕ)
    (hb : b < (i :: μ).length) :
    rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ) (dotE D Sc (i :: μ) b ^ d)) =
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) b d := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    (whiskerWordRingHom D Sc (i :: μ) σ (dotE D Sc (i :: μ) b ^ d)) = _
  rw [map_pow, whiskerWordRingHom_apply, dotE_whiskerRight D Sc (i :: μ) σ b hb]
  rfl

private theorem qpEval_power_difference (i : I) (μ σ z : List I) (a d : ℕ)
    (ha : a < μ.length) (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ)))) :
    qpEval D Sc cutoff i μ σ z h
      ((dotE D Sc (i :: μ) (a + 1) ^ d - dotE D Sc (i :: μ) 0 ^ d) ≫ f) =
    projection D Sc cutoff i (μ ++ σ) z
      ((sourceDotPower D Sc cutoff (i :: (μ ++ σ)) (a + 1) d -
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) 0 d) ≫
        (rightContext D Sc cutoff σ _ _ (affineUnit D Sc cutoff _ _ f) ≫
          (relation D Sc cutoff i (μ ++ σ) ≫ h))) := by
  change projection D Sc cutoff i (μ ++ σ) z
    (rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ)
        ((dotE D Sc (i :: μ) (a + 1) ^ d - dotE D Sc (i :: μ) 0 ^ d) ≫ f)) ≫
      (relation D Sc cutoff i (μ ++ σ) ≫ h)) = _
  rw [affineUnit_comp, rightContext_comp, Category.assoc]
  have he : rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ)
        (dotE D Sc (i :: μ) (a + 1) ^ d - dotE D Sc (i :: μ) 0 ^ d)) =
      sourceDotPower D Sc cutoff (i :: (μ ++ σ)) (a + 1) d -
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) 0 d := by
    rw [map_sub, map_sub,
      rightContext_affineUnit_dotPower D Sc cutoff i μ σ (a + 1) d (by simp; omega),
      rightContext_affineUnit_dotPower D Sc cutoff i μ σ 0 d (by simp)]
  rw [he]

/-- Square cancellation for `qpEval` in arbitrary right contexts. -/
theorem qpEval_square_difference_cancel (i : I) (μ σ z : List I) (a : ℕ)
    (ha : a < μ.length) (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ))))
    (hf : qpEval D Sc cutoff i μ σ z h
      ((dotE D Sc (i :: μ) (a + 1) ^ 2 - dotE D Sc (i :: μ) 0 ^ 2) ≫ f) = 0) :
    qpEval D Sc cutoff i μ σ z h f = 0 := by
  rw [qpEval_power_difference D Sc cutoff i μ σ z a 2 ha] at hf
  exact projection_power_difference_cancel D Sc cutoff i (μ ++ σ) z a 2
    ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) _) (by decide) _ hf

/-- The odd source difference preserves zero evaluation, using total-parity naturality. -/
theorem qpEval_source_difference_zero (i : I) (μ σ z : List I) (a : ℕ)
    (ha : a < μ.length) (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ))))
    (hf : qpEval D Sc cutoff i μ σ z h f = 0) :
    qpEval D Sc cutoff i μ σ z h
      ((dotE D Sc (i :: μ) (a + 1) - dotE D Sc (i :: μ) 0) ≫ f) = 0 := by
  have he := qpEval_power_difference D Sc cutoff i μ σ z a 1 ha h f
  simp only [pow_one] at he
  rw [he]
  exact projection_source_difference_zero D Sc cutoff i (μ ++ σ) z a _ hf

/-- The full-coefficient all-prefix relation in evaluation coordinates. -/
theorem qpEval_prefix_zero (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: (μ ++ [i])) ++ σ) z) :
    qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) = 0 := by
  have hK := allPrefix_relation_context D Sc cutoff i μ σ z h
  change projection D Sc cutoff i ((μ ++ [i]) ++ σ) z
    (rightContext D Sc cutoff σ (i :: (μ ++ [i])) (i :: (μ ++ [i]))
      (affineUnit D Sc cutoff (i :: (μ ++ [i])) ((μ ++ [i]) ++ [i])
        (moveHom D Sc i [] (μ ++ [i])) ≫
        affineUnit D Sc cutoff ((μ ++ [i]) ++ [i]) (i :: (μ ++ [i]))
          (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) ≫
      relation D Sc cutoff i ((μ ++ [i]) ++ σ) ≫ h) = 0 at hK
  rw [← affineUnit_comp D Sc cutoff
    (v := i :: (μ ++ [i])) (w := (μ ++ [i]) ++ [i]) (z := i :: (μ ++ [i]))
    (moveHom D Sc i [] (μ ++ [i]))
    (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))] at hK
  exact hK

private theorem odd_expansion {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {x y : C} (Δ E : End x) (V : x ⟶ y) (τ : End y) (T : y ⟶ x) (s : k) :
    Δ ≫ (s • (E ≫ (V ≫ T)) - Δ ≫ (V ≫ (τ ≫ T))) =
      (s • (Δ ≫ E ≫ V) - Δ ≫ Δ ≫ V ≫ τ) ≫ T := by
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Linear.comp_smul,
    Linear.smul_comp, Category.assoc]

/-- Repeated-odd recursion. Both prefix signs are retained until their product is one.
The new last letter makes the old word nonempty even when the prefix is empty. -/
theorem qp_repeated_odd (i : I) (hi : D.parity i = 1) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: (μ ++ [i])) ++ σ) z) :
    qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫ lastToFirstHom D Sc i (μ ++ [i])) =
    qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (((dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) -
        dotE D Sc (i :: (μ ++ [i])) 0) ^ 2) ≫
        moveWhisker D Sc i μ ≫
          (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) := by
  let E := dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) -
    dotE D Sc (i :: (μ ++ [i])) 0
  let Δ := dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) ^ 2 -
    dotE D Sc (i :: (μ ++ [i])) 0 ^ 2
  let s := SKM.zsign k (D.parity i * wordSumParity D μ)
  let A : End ((pres D Sc).obj (ob D (i :: (μ ++ [i])))) :=
    moveWhisker D Sc i μ ≫ (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))
  let B := moveWhisker D Sc i μ ≫ lastToFirstHom D Sc i (μ ++ [i])
  have hK := qpEval_prefix_zero D Sc cutoff i μ σ z h
  have hzero : qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (Δ ≫ (s • (E ≫ A) - Δ ≫ B)) = 0 := by
    change qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) = 0 at hK
    rw [moveHom_append_self, moveWhisker_comp_sameIntertwiner_odd D Sc i hi μ] at hK
    dsimp only [A, B]
    rw [lastToFirstHom_append_self]
    exact (congrArg (qpEval D Sc cutoff i (μ ++ [i]) σ z h)
      (odd_expansion Δ E (moveWhisker D Sc i μ)
        (crossE D Sc (μ ++ [i] ++ [i]) μ.length)
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i])) s)).trans hK
  have hc := qpEval_square_difference_cancel D Sc cutoff i (μ ++ [i]) σ z μ.length
    (by simp) h (s • (E ≫ A) - Δ ≫ B) hzero
  have hp := qpEval_source_difference_zero D Sc cutoff i (μ ++ [i]) σ z μ.length
    (by simp) h (s • (E ≫ A) - Δ ≫ B) hc
  have hDE : Δ * E = E * Δ :=
    squareDiff_mul_sub_comm (dotE_last_mul_first D Sc i μ) (zsign_mul_self _)
  have hED : E ≫ Δ ≫ B = Δ ≫ E ≫ B := by
    rw [← Category.assoc E Δ B, ← Category.assoc Δ E B]
    exact congrArg (fun f : End ((pres D Sc).obj (ob D (i :: (μ ++ [i])))) => f ≫ B) hDE
  change qpEval D Sc cutoff i (μ ++ [i]) σ z h (E ≫ (s • (E ≫ A) - Δ ≫ B)) = 0 at hp
  rw [Preadditive.comp_sub, Linear.comp_smul, hED, map_sub, map_smul, sub_eq_zero] at hp
  rw [moveHom_lastToFirstHom_append_self_odd D Sc i hi μ, map_smul]
  change s • qpEval D Sc cutoff i (μ ++ [i]) σ z h (Δ ≫ E ≫ B) = _
  rw [← hp, smul_smul, show s * s = 1 from zsign_mul_self _, one_smul]
  congr 1
  simp only [E, A, pow_two, End.mul_def, Category.assoc]

end OddMath.QuiverHecke.ELVOld
