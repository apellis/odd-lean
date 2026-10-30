/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQPRepeated
import OddMath.QuiverHecke.CyclotomicAction.ELVOldRightContext
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance

/-!
# Coefficient balance for the ELV old-generator P map

The coefficient-only balance needed in `DeformedGlobalQP.md` §4. For the
old-generator morphism `W = affineUnit(lastToFirstHom) ≫ relation`, the total
parity is the sum of the crossing-word parity and the full relation parity.
The theorem `oldGenerator_scalar_balance` moves an arbitrary ELV coefficient
through `W`, with this total-parity twist and the right-context inclusion.

Supercommutativity is proved, not assumed: exterior-generator anticommutation
extends to the parity pieces, then to the polynomial/exterior model and its
homogeneous ELV quotient. The signed box product supplies the remaining affine
Koszul sign. No old cyclotomic relation is killed in this calculation, and no
homogeneity assumption is imposed on the coefficient in the final theorem.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVPScalar
universe u
variable {k M : Type u} [CommRing k] [AddCommGroup M] [Module k M]

private theorem exterior_ι_pow {n : ℕ} {b : ExteriorAlgebra k M}
    (hb : b ∈ (ExteriorAlgebra.ι k : M →ₗ[k] ExteriorAlgebra k M).range ^ n) (m : M) :
    ExteriorAlgebra.ι k m * b = koszulSign 1 (n : ZMod 2) • (b * ExteriorAlgebra.ι k m) := by
  induction hb using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y n hx hy ihx ihy => simp only [mul_add, add_mul, ihx, ihy, smul_add]
  | mem_mul a ha n x hx ih =>
    obtain ⟨a, rfl⟩ := ha
    have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := k) m a)
    rw [← mul_assoc, h, neg_mul, mul_assoc, ih, mul_smul_comm, ← mul_assoc]
    simp only [Nat.cast_succ, koszulSign_add_right, koszulSign_one_one,
      mul_neg, neg_smul, mul_one]

private theorem exterior_pow_comm {n l : ℕ} {a b : ExteriorAlgebra k M}
    (ha : a ∈ (ExteriorAlgebra.ι k : M →ₗ[k] ExteriorAlgebra k M).range ^ n)
    (hb : b ∈ (ExteriorAlgebra.ι k : M →ₗ[k] ExteriorAlgebra k M).range ^ l) :
    a * b = koszulSign (n : ZMod 2) (l : ZMod 2) • (b * a) := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y n hx hy ihx ihy => simp only [mul_add, add_mul, ihx, ihy, smul_add]
  | mem_mul a ha n x hx ih =>
    obtain ⟨a, rfl⟩ := ha
    rw [mul_assoc, ih, mul_smul_comm, ← mul_assoc, exterior_ι_pow hb,
      smul_mul_assoc, mul_assoc, smul_smul]
    simp only [Nat.cast_succ, koszulSign_add_left]

/-- Exterior parity pieces supercommute over any commutative ground ring. -/
theorem exterior_comm {p q : ZMod 2} {a b : ExteriorAlgebra k M}
    (ha : a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm k M) p)
    (hb : b ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm k M) q) :
    a * b = koszulSign p q • (b * a) := by
  induction ha using Submodule.iSup_induction' with
  | zero => simp
  | add x y hx hy ihx ihy => simp only [add_mul, mul_add, ihx, ihy, smul_add]
  | mem n a ha =>
    induction hb using Submodule.iSup_induction' with
    | zero => simp
    | add x y hx hy ihx ihy => simp only [add_mul, mul_add, ihx, ihy, smul_add]
    | mem m b hb =>
      obtain ⟨n, rfl⟩ := n
      obtain ⟨m, rfl⟩ := m
      exact exterior_pow_comm ha hb
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)

/-- The polynomial factor is even, so exterior supercommutativity extends by base change. -/
theorem polynomialExterior_comm {p q : ZMod 2} {a b : SKM.SYM.PolynomialExterior D k}
    (ha : a ∈ SKM.SYM.polynomialExteriorParity D k p)
    (hb : b ∈ SKM.SYM.polynomialExteriorParity D k q) :
    a * b = koszulSign p q • (b * a) := by
  change a ∈ (SKM.SYM.exteriorParity D k p).baseChange (MvPolynomial (I × ℕ) k) at ha
  change b ∈ (SKM.SYM.exteriorParity D k q).baseChange (MvPolynomial (I × ℕ) k) at hb
  rw [Submodule.baseChange_eq_span] at ha hb
  induction ha using Submodule.span_induction with
  | zero => simp
  | add x y hx hy ihx ihy => simp only [add_mul, mul_add, ihx, ihy, smul_add]
  | smul c x hx ih => simp only [smul_mul_assoc, mul_smul_comm, ih, smul_comm c]
  | mem a ha =>
    obtain ⟨a, ha, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | zero => simp
    | add x y hx hy ihx ihy => simp only [add_mul, mul_add, ihx, ihy, smul_add]
    | smul c x hx ih => simp only [smul_mul_assoc, mul_smul_comm, ih, smul_comm c]
    | mem b hb =>
      obtain ⟨b, hb, rfl⟩ := hb
      change (1 ⊗ₜ[k] a : SKM.SYM.PolynomialExterior D k) * (1 ⊗ₜ[k] b) =
        koszulSign p q • ((1 ⊗ₜ[k] b) * (1 ⊗ₜ[k] a))
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [exterior_comm ha hb, TensorProduct.tmul_smul]
/-- The coefficient quotient commutes with homogeneous projection. -/
theorem elvModelQuotient_proj (cutoff : I → ℕ) (p : ZMod 2)
    (a : SKM.SYM.PolynomialExterior D k) :
    SKM.SYM.elvModelQuotient (k := k) D cutoff (GradedAlgebra.proj (SKM.SYM.polynomialExteriorParity D k) p a) =
      GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p
        (SKM.SYM.elvModelQuotient (k := k) D cutoff a) := by
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.polynomialExteriorParity D k)
    (by simp) ?_ ?_ a
  · intro q a
    by_cases h : q = p
    · subst q
      simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ a.property,
        DirectSum.decompose_of_mem_same _ (SKM.SYM.elvModelQuotient_mem D a.property)]
    · simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne _ a.property h,
        DirectSum.decompose_of_mem_ne _ (SKM.SYM.elvModelQuotient_mem D a.property) h, map_zero]
  · intro a b ha hb
    simp only [map_add, ha, hb]

/-- Every homogeneous ELV coefficient has a homogeneous polynomial/exterior lift. -/
theorem elv_homogeneous_lift (cutoff : I → ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    ∃ b ∈ SKM.SYM.polynomialExteriorParity D k p, SKM.SYM.elvModelQuotient (k := k) D cutoff b = a := by
  obtain ⟨a, rfl⟩ := ((RingCon.mkₐ_surjective (α := k)
    (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon).comp
    (SKM.SYM.polynomialExteriorEquiv D k).symm.surjective) a
  refine ⟨GradedAlgebra.proj (SKM.SYM.polynomialExteriorParity D k) p a,
    (DirectSum.decompose (SKM.SYM.polynomialExteriorParity D k) a p).property, ?_⟩
  change SKM.SYM.elvModelQuotient (k := k) D cutoff a ∈
    SKM.SYM.elvCoefficientParity D cutoff p at ha
  change SKM.SYM.elvModelQuotient (k := k) D cutoff _ =
    SKM.SYM.elvModelQuotient (k := k) D cutoff a
  rw [elvModelQuotient_proj, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ ha]

/-- Graded commutativity of the full ELV coefficient algebra. -/
theorem elv_comm (cutoff : I → ℕ) {p q : ZMod 2}
    {a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p)
    (hb : b ∈ SKM.SYM.elvCoefficientParity D cutoff q) :
    a * b = koszulSign p q • (b * a) := by
  obtain ⟨a, ha', rfl⟩ := elv_homogeneous_lift D cutoff ha
  obtain ⟨b, hb', rfl⟩ := elv_homogeneous_lift D cutoff hb
  simpa only [map_mul, map_zsmul] using
    congrArg (SKM.SYM.elvModelQuotient (k := k) D cutoff) (polynomialExterior_comm D ha' hb')
variable (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
open ELVOld

def scalar (v : List I) : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
    hom D Sc cutoff v v :=
  (TensorProduct.mk k _ _).flip (𝟙 ((pres D Sc).obj (ob D v)))

theorem scalar_mem (v : List I) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    scalar D Sc cutoff v a ∈ parity (R := k) _ _ p := by
  have h := BoxProd.tmul_mem_parity
    (X := obj D Sc cutoff v) (Y := obj D Sc cutoff v) ha
    (id_mem (R := k) ((pres D Sc).obj (ob D v)))
  change scalar D Sc cutoff v a ∈ parity (R := k) _ _ (p + 0) at h
  simpa only [add_zero] using h

private theorem scalar_induction_hom {v w : List I} {P : hom D Sc cutoff v w → Prop}
    (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (obj D Sc cutoff v).snd ⟶ (obj D Sc cutoff w).snd),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

theorem scalar_slide_homogeneous {v w : List I} {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) (f : hom D Sc cutoff v w) :
    f ≫ scalar D Sc cutoff w a = scalar D Sc cutoff v a ≫ twist k p f := by
  induction f using scalar_induction_hom D Sc cutoff with
  | zero => simp only [Limits.zero_comp, map_zero, Limits.comp_zero]
  | add f g hf hg => simp only [Preadditive.add_comp, map_add, Preadditive.comp_add, hf, hg]
  | tmul r s b f hb hf =>
    have ht := BoxProd.tmul_mem_parity (X := obj D Sc cutoff v)
      (Y := obj D Sc cutoff w) hb hf
    change BoxProd.tmulHom b f ∈ parity (R := k) _ _ (r + s) at ht
    rw [twist_of_mem p ht, ← koszulSign_smul, Preadditive.comp_zsmul]
    change BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w) b f ≫
      BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w) a (𝟙 _) =
      koszulSign p (r + s) •
        (BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff v) a (𝟙 _) ≫
          BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w) b f)
    rw [BoxProd.tmulHom_comp_tmulHom hb f a (id_mem (R := k) _),
      BoxProd.tmulHom_comp_tmulHom ha (𝟙 _) b hf]
    simp only [koszulSign_zero_right, one_smul, Category.comp_id, Category.id_comp]
    change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff at b
    change b ∈ SKM.SYM.elvCoefficientParity D cutoff r at hb
    change (a * b) ⊗ₜ[k] f = koszulSign p (r + s) • (koszulSign p s • ((b * a) ⊗ₜ[k] f))
    rw [elv_comm D cutoff ha hb, smul_smul,
      koszulSign_add_right, mul_assoc, koszulSign_mul_self, mul_one]
    exact map_zsmul ((TensorProduct.mk k _ _).flip f) _ _
/-- An arbitrary coefficient slides across any homogeneous coefficient-category morphism. -/
theorem scalar_slide {v w : List I} {q : ZMod 2} {f : hom D Sc cutoff v w}
    (hf : f ∈ parity (R := k) _ _ q)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    f ≫ scalar D Sc cutoff w a = twist k q (scalar D Sc cutoff v a) ≫ f := by
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff)
    (by simp) ?_ ?_ a
  · intro p a
    rw [scalar_slide_homogeneous D Sc cutoff a.property,
      twist_of_mem p hf, twist_of_mem q (scalar_mem D Sc cutoff v a.property),
      Linear.comp_smul, Linear.smul_comp, mul_comm p q]
  · intro a b ha hb
    simp only [map_add, Preadditive.comp_add, Preadditive.add_comp, ha, hb]

theorem insert_scalar (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    insert D Sc cutoff i v v (scalar D Sc cutoff v a) = scalar D Sc cutoff (i :: v) a := by
  exact congrArg (fun f => a ⊗ₜ[k] f)
    (MonoidalSupercategory.whiskerLeft_id (R := k) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D v)))

theorem rightContext_scalar (σ v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    rightContext D Sc cutoff σ v v (scalar D Sc cutoff v a) = scalar D Sc cutoff (v ++ σ) a := by
  exact congrArg (fun f => a ⊗ₜ[k] f)
    (MonoidalSupercategory.id_whiskerRight (R := k) ((pres D Sc).obj (ob D v)) ((pres D Sc).obj (ob D σ)))

theorem rightContext_twist_scalar (σ v : List I) (q : ZMod 2)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    rightContext D Sc cutoff σ v v (twist k q (scalar D Sc cutoff v a)) =
      twist k q (scalar D Sc cutoff (v ++ σ) a) := by
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff)
    (by simp) ?_ ?_ a
  · intro p a
    rw [twist_of_mem q (scalar_mem D Sc cutoff v a.property), map_smul,
      rightContext_scalar, twist_of_mem q (scalar_mem D Sc cutoff (v ++ σ) a.property)]
  · intro a b ha hb
    simp only [map_add, ha, hb]

theorem affineUnit_mem {v w : List I} {q : ZMod 2}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ parity (R := k) _ _ q) :
    affineUnit D Sc cutoff v w f ∈ parity (R := k) _ _ q := by
  have h := BoxProd.tmul_mem_parity (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w)
    (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
      parity (R := k) (obj D Sc cutoff v).fst (obj D Sc cutoff w).fst 0 from
      (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
        SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem)) hf
  change affineUnit D Sc cutoff v w f ∈ parity (R := k) _ _ (0 + q) at h
  simpa only [zero_add] using h

/-- Universal coefficient-only balance for P: arbitrary word, cutoff and coefficient. -/
theorem oldGenerator_scalar_balance (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (affineUnit D Sc cutoff (v ++ [i]) (i :: v) (lastToFirstHom D Sc i v) ≫
      ELVOld.relation D Sc cutoff i v) ≫ insert D Sc cutoff i v v (scalar D Sc cutoff v a) =
    rightContext D Sc cutoff [i] v v
      (twist k (D.parity i * wordSumParity D v + (cutoff i : ZMod 2) * D.parity i)
        (scalar D Sc cutoff v a)) ≫
      (affineUnit D Sc cutoff (v ++ [i]) (i :: v) (lastToFirstHom D Sc i v) ≫
        ELVOld.relation D Sc cutoff i v) := by
  rw [insert_scalar, rightContext_twist_scalar]
  exact scalar_slide D Sc cutoff
    (comp_mem (affineUnit_mem D Sc cutoff (lastToFirstHom_mem D Sc v))
      (relation_mem_parity D Sc cutoff i v)) a
end OddMath.QuiverHecke.ELVPScalar
