/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalSlideAlgebra

/-!
# The dot slides on two inductions from every height

The functor half of `Categorification/KLR/CyclotomicAction/GlobalSlides.lean` at a fixed
height. On the same-colour composition corner `T = C θ(1)` of `GlobalHeightCrossing`, signed
right multiplication by the new last dot `y₂` and by the appended dot `y₁ = φ(y)` are
superbimodule endomorphisms of parity `|i|` (`heightCompositionRightMul`). Along the comparison
`F ≅ T ⊗ -` of the two inductions, the dot of the outer induction whiskered by the inner one
becomes `y₂`, the inner dot under the outer induction becomes `y₁`
(`heightComparison_dot_outer`, `heightComparison_dot_inner`). The algebra slides of
`GlobalSlideAlgebra` then give, with `s = (-1)^{|i|}` and `ψ` the crossing,

  `x₂ ψ - s ψ x₁ = -1`,  `ψ x₂ - s x₁ ψ = -1`

for the components on every module (`heightInduction_slide_left`,
`heightInduction_slide_right`); with the Rouquier crossing `t = -ψ` these are the slides of
`SuperRouquierLoc`.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section RightMul
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "C" => heightAlgebra D Sc a (n + 1 + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GC" => heightParity D Sc a ha (n + 1 + 1)
local notation "θ" => fun r => heightAppend D Sc a i (n + 1) (heightAppend D Sc a i n r)
local notation "T" => heightCompositionCorner D Sc i i a ha n
local notation "d" => D.parity i

/-- Hypotheses on an element `u` for signed right multiplication to be an endomorphism of the
same-colour composition corner: parity `|i|`, the corner is preserved, and `u`
supercommutes with the image of the base algebra. -/
structure CornerMulData (u : C) : Prop where
  mem : u ∈ GC d
  corner : ∀ x : C, x * θ 1 = x → (x * u) * θ 1 = x * u
  comm : ∀ {p : ZMod 2} {r : heightAlgebra D Sc a n}, r ∈ GA p →
    θ r * u = koszulSign p d • (u * θ r)

variable {i a ha n} in
private theorem cornerMul_mem {u : C} (hu : CornerMulData D Sc i a ha n u) (x : C)
    (hx : x ∈ heightCompositionCornerSubmodule D Sc i i a n) :
    x * u ∈ heightCompositionCornerSubmodule D Sc i i a n :=
  hu.corner x hx

/-- Parity sign followed by right multiplication by `u`. -/
def heightCompositionRightMulLinear {u : C} (hu : CornerMulData D Sc i a ha n u) :
    (T).toSVec ⟶ (T).toSVec :=
  SVec.ofHom ((T).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GC).ract u) (cornerMul_mem D Sc hu)

theorem heightCompositionRightMulLinear_parity {u : C} (hu : CornerMulData D Sc i a ha n u) :
    heightCompositionRightMulLinear D Sc i a ha n hu ∈ SVec.parityHom (T).toSVec (T).toSVec d := by
  change heightCompositionRightMulLinear D Sc i a ha n hu ∈ parity (R := k) (T).toSVec (T).toSVec d
  unfold heightCompositionRightMulLinear
  have hd := SVec.restrictHom_mem (hU := heightCompositionCorner_odd_mem D Sc i i a ha n)
    (hU' := heightCompositionCorner_odd_mem D Sc i i a ha n)
    ((SuperBimodule.regular GC).ract_mem d u hu.mem) (cornerMul_mem D Sc hu)
  have h2 := Supercategory.comp_mem (SVec.sgn_mem (T).toSVec d) hd
  rw [zero_add] at h2
  exact h2

private theorem rightMul_sgn_action {p : ZMod 2} {f : (T).toSVec ⟶ (T).toSVec}
    (hf : f ∈ SVec.parityHom (T).toSVec (T).toSVec p) (x : (T).toSVec) :
    (T).toSVec.sgn d (f x) = sign k (p * d) • f ((T).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

theorem heightCompositionRightMulLinear_isHom {u : C} (hu : CornerMulData D Sc i a ha n u) :
    SuperBimodule.IsHom T T (heightCompositionRightMulLinear D Sc i a ha n hu) := by
  apply (SuperBimodule.isHom_iff_of_mem (heightCompositionRightMulLinear_parity D Sc i a ha n hu)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := rightMul_sgn_action D Sc i a ha n ((T).lact_mem p b hb) x
    apply Subtype.ext
    change ((T).toSVec.sgn d ((T).lact b x)).val * u =
      sign k (p * d) • (b * (((T).toSVec.sgn d x).val * u))
    rw [h]
    change (sign k (p * d) • (b * ((T).toSVec.sgn d x).val)) * u = _
    rw [smul_mul_assoc, mul_assoc]
  · intro r
    induction r using SuperBimodule.alg_induction_on GA with
    | zero => simp
    | add r s hr hs => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hr, hs]
    | hom p r hr =>
      apply SVec.hom_ext
      intro x
      have h := rightMul_sgn_action D Sc i a ha n ((T).ract_mem p r hr) x
      apply Subtype.ext
      change ((T).toSVec.sgn d ((T).ract r x)).val * u =
        (((T).toSVec.sgn d x).val * u) *
          heightAppend D Sc a i (n + 1) (heightAppend D Sc a i n r)
      rw [h]
      change (sign k (p * d) • (((T).toSVec.sgn d x).val *
        heightAppend D Sc a i (n + 1) (heightAppend D Sc a i n r))) * u = _
      rw [smul_mul_assoc, mul_assoc, hu.comm hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul,
        mul_assoc]

/-- **Signed right multiplication** as a homogeneous endomorphism of the corner. -/
def heightCompositionRightMul {u : C} (hu : CornerMulData D Sc i a ha n u) : T ⟶ T :=
  ⟨heightCompositionRightMulLinear D Sc i a ha n hu,
    heightCompositionRightMulLinear_isHom D Sc i a ha n hu⟩

/-- The new last dot `y₂` satisfies the corner hypotheses. -/
theorem cornerMulData_lastDot :
    CornerMulData D Sc i a ha n (heightLastDot D Sc a i (n + 1)) where
  mem := heightLastDot_parity D Sc a i ha (n + 1)
  corner x hx := by
    have h := heightLastDot_comm D Sc a i ha (n + 1)
      (heightAppend_parity D Sc a ha i n (SetLike.one_mem_graded GA))
    rw [koszulSign_zero_left, one_smul] at h
    rw [mul_assoc, ← h, ← mul_assoc, hx]
  comm hr := heightLastDot_comm D Sc a i ha (n + 1) (heightAppend_parity D Sc a ha i n hr)

/-- The appended dot `y₁ = φ(y)` satisfies the corner hypotheses. -/
theorem cornerMulData_appendDot :
    CornerMulData D Sc i a ha n (heightAppend D Sc a i (n + 1) (heightLastDot D Sc a i n)) where
  mem := heightAppend_parity D Sc a ha i (n + 1) (heightLastDot_parity D Sc a i ha n)
  corner x _ := by
    rw [mul_assoc, ← map_mul, (heightLastDot_corner D Sc a i n).2]
  comm {p} {r} hr := by
    rw [← map_mul, heightLastDot_comm D Sc a i ha n hr, map_zsmul, map_mul]

end RightMul

/-! ### Signs and additivity -/

section Additive
variable {a : I → _root_.Polynomial k} {ha : CyclotomicPolynomialParity D a} {m n : ℕ}

end Additive

/-! ### The slides on the corner -/

section CornerSlides
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "T" => heightCompositionCorner D Sc i i a ha n
local notation "d" => D.parity i
local notation "Dr" => heightCompositionRightMul D Sc i a ha n (cornerMulData_lastDot D Sc i a ha n)
local notation "Dl" => heightCompositionRightMul D Sc i a ha n (cornerMulData_appendDot D Sc i a ha n)
local notation "Cr" => heightCompositionSuperCrossing D Sc i i a ha n

end CornerSlides

/-! ### Transport along the comparison -/

section Transport
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "T" => heightCompositionCorner D Sc i i a ha n
local notation "Pc" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Qc" => heightInductionCorner D Sc i a ha n
local notation "d" => D.parity i
local notation "Dr" => heightCompositionRightMul D Sc i a ha n (cornerMulData_lastDot D Sc i a ha n)
local notation "Dl" => heightCompositionRightMul D Sc i a ha n (cornerMulData_appendDot D Sc i a ha n)
local notation "Cr" => heightCompositionSuperCrossing D Sc i i a ha n
local notation "iso" => heightInductionCompositionIso D Sc i i a ha n
local notation "e" => heightInductionFunctorComparison D Sc i i a ha n

/-- The comparison component, written on tensor products. -/
def heightComparisonHom (M : HeightModules D Sc a ha n) : tensor Pc (tensor Qc M) ⟶ tensor T M :=
  (assoc Pc Qc M).inv ≫ whiskerRight (iso).hom M

/-- Its inverse, written on tensor products. -/
def heightComparisonInv (M : HeightModules D Sc a ha n) : tensor T M ⟶ tensor Pc (tensor Qc M) :=
  whiskerRight (iso).inv M ≫ (assoc Pc Qc M).hom

end Transport

end OddMath.QuiverHecke.CyclotomicAction
