/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightSlides
import OddMath.QuiverHecke.CyclotomicAction.GlobalMixedSlideAlgebra

/-!
# The distinct-colour dot slides on two inductions from every height

The functor half of the distinct-colour slides (1.8) of Brundan–Ellis, arXiv:1701.04133v2,
Definition 1.5, at a fixed height. On the two-colour composition corner `T_{ij} = C θ(1)`,
`θ = φᵢ ∘ φⱼ`, of `GlobalHeightCrossing`, signed right multiplication by the new last dot
`y_i` and by the appended dot `φᵢ(y_j)` are superbimodule endomorphisms of parities `|i|` and
`|j|` (`heightTwoColourRightMul`). Along the comparison of `Ind_j ⋙ Ind_i` with `T_{ij} ⊗ -`
the outer dot becomes `y_i` and the inner dot becomes `φᵢ(y_j)`
(`heightTwoColourComparison_dot_outer_app`, `heightTwoColourComparison_dot_inner_app`). The
algebra slides of `GlobalMixedSlideAlgebra` then give, with `ε = (-1)^{|i||j|}` and `ψ` the
crossing, in diagrammatic order,

  `x_i^{out} ψ = ε ψ x_i^{in}`,  `ψ x_j^{out} = ε x_j^{in} ψ`

for the components on every module (`heightInduction_slide_left_ne`,
`heightInduction_slide_right_ne`).
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section RightMul
variable (i j c : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "C" => heightAlgebra D Sc a (n + 1 + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GC" => heightParity D Sc a ha (n + 1 + 1)
local notation "θ" => fun r => heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n r)
local notation "T" => heightCompositionCorner D Sc i j a ha n
local notation "d" => D.parity c

/-- Hypotheses on an element `u` for signed right multiplication to be an endomorphism of the
two-colour composition corner: parity `|c|`, the corner is preserved, and `u` supercommutes
with the image of the base algebra. -/
structure TwoColourCornerMulData (u : C) : Prop where
  mem : u ∈ GC d
  corner : ∀ x : C, x * θ 1 = x → (x * u) * θ 1 = x * u
  comm : ∀ {p : ZMod 2} {r : heightAlgebra D Sc a n}, r ∈ GA p →
    θ r * u = koszulSign p d • (u * θ r)

variable {i j c a ha n} in
private theorem twoColourCornerMul_mem {u : C} (hu : TwoColourCornerMulData D Sc i j c a ha n u)
    (x : C) (hx : x ∈ heightCompositionCornerSubmodule D Sc i j a n) :
    x * u ∈ heightCompositionCornerSubmodule D Sc i j a n :=
  hu.corner x hx

/-- Parity sign followed by right multiplication by `u`. -/
def heightTwoColourRightMulLinear {u : C} (hu : TwoColourCornerMulData D Sc i j c a ha n u) :
    (T).toSVec ⟶ (T).toSVec :=
  SVec.ofHom ((T).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GC).ract u) (twoColourCornerMul_mem D Sc hu)

theorem heightTwoColourRightMulLinear_parity {u : C}
    (hu : TwoColourCornerMulData D Sc i j c a ha n u) :
    heightTwoColourRightMulLinear D Sc i j c a ha n hu ∈
      SVec.parityHom (T).toSVec (T).toSVec d := by
  change heightTwoColourRightMulLinear D Sc i j c a ha n hu ∈
    parity (R := k) (T).toSVec (T).toSVec d
  unfold heightTwoColourRightMulLinear
  have hd := SVec.restrictHom_mem (hU := heightCompositionCorner_odd_mem D Sc i j a ha n)
    (hU' := heightCompositionCorner_odd_mem D Sc i j a ha n)
    ((SuperBimodule.regular GC).ract_mem d u hu.mem) (twoColourCornerMul_mem D Sc hu)
  have h2 := Supercategory.comp_mem (SVec.sgn_mem (T).toSVec d) hd
  rw [zero_add] at h2
  exact h2

private theorem twoColourRightMul_sgn_action {p : ZMod 2} {f : (T).toSVec ⟶ (T).toSVec}
    (hf : f ∈ SVec.parityHom (T).toSVec (T).toSVec p) (x : (T).toSVec) :
    (T).toSVec.sgn d (f x) = sign k (p * d) • f ((T).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

theorem heightTwoColourRightMulLinear_isHom {u : C}
    (hu : TwoColourCornerMulData D Sc i j c a ha n u) :
    SuperBimodule.IsHom T T (heightTwoColourRightMulLinear D Sc i j c a ha n hu) := by
  apply (SuperBimodule.isHom_iff_of_mem
    (heightTwoColourRightMulLinear_parity D Sc i j c a ha n hu)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := twoColourRightMul_sgn_action D Sc i j c a ha n ((T).lact_mem p b hb) x
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
      have h := twoColourRightMul_sgn_action D Sc i j c a ha n ((T).ract_mem p r hr) x
      apply Subtype.ext
      change ((T).toSVec.sgn d ((T).ract r x)).val * u =
        (((T).toSVec.sgn d x).val * u) *
          heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n r)
      rw [h]
      change (sign k (p * d) • (((T).toSVec.sgn d x).val *
        heightAppend D Sc a i (n + 1) (heightAppend D Sc a j n r))) * u = _
      rw [smul_mul_assoc, mul_assoc, hu.comm hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul,
        mul_assoc]

/-- **Signed right multiplication** as a homogeneous endomorphism of the two-colour corner. -/
def heightTwoColourRightMul {u : C} (hu : TwoColourCornerMulData D Sc i j c a ha n u) : T ⟶ T :=
  ⟨heightTwoColourRightMulLinear D Sc i j c a ha n hu,
    heightTwoColourRightMulLinear_isHom D Sc i j c a ha n hu⟩

/-- The new last dot `y_i` satisfies the corner hypotheses. -/
theorem twoColourCornerMulData_lastDot :
    TwoColourCornerMulData D Sc i j i a ha n (heightLastDot D Sc a i (n + 1)) where
  mem := heightLastDot_parity D Sc a i ha (n + 1)
  corner x hx := by
    have h := heightLastDot_comm D Sc a i ha (n + 1)
      (heightAppend_parity D Sc a ha j n (SetLike.one_mem_graded GA))
    rw [koszulSign_zero_left, one_smul] at h
    rw [mul_assoc, ← h, ← mul_assoc, hx]
  comm hr := heightLastDot_comm D Sc a i ha (n + 1) (heightAppend_parity D Sc a ha j n hr)

/-- The appended dot `φᵢ(y_j)` satisfies the corner hypotheses. -/
theorem twoColourCornerMulData_appendDot :
    TwoColourCornerMulData D Sc i j j a ha n
      (heightAppend D Sc a i (n + 1) (heightLastDot D Sc a j n)) where
  mem := heightAppend_parity D Sc a ha i (n + 1) (heightLastDot_parity D Sc a j ha n)
  corner x _ := by
    rw [mul_assoc, ← map_mul, (heightLastDot_corner D Sc a j n).2]
  comm {p} {r} hr := by
    rw [← map_mul, heightLastDot_comm D Sc a j ha n hr, map_zsmul, map_mul]

end RightMul

/-! ### The slides on the corners -/

section CornerSlides
variable {i j : I} (hij : i ≠ j) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)
include hij

local notation "d" => D.parity i * D.parity j
local notation "ε" => koszulSign (D.parity i) (D.parity j)
local notation "Cr" => heightCompositionSuperCrossing D Sc i j a ha n
local notation "Dr" => heightTwoColourRightMul D Sc i j i a ha n
  (twoColourCornerMulData_lastDot D Sc i j a ha n)
local notation "Dl" => heightTwoColourRightMul D Sc j i i a ha n
  (twoColourCornerMulData_appendDot D Sc j i a ha n)
local notation "Er" => heightTwoColourRightMul D Sc j i j a ha n
  (twoColourCornerMulData_lastDot D Sc j i a ha n)
local notation "El" => heightTwoColourRightMul D Sc i j j a ha n
  (twoColourCornerMulData_appendDot D Sc i j a ha n)

end CornerSlides

/-! ### Transport along the comparison -/

section Transport
variable (i j : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "T" => heightCompositionCorner D Sc i j a ha n
local notation "Pc" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Qc" => heightInductionCorner D Sc j a ha n
local notation "iso" => heightInductionCompositionIso D Sc i j a ha n
local notation "Dr" => heightTwoColourRightMul D Sc i j i a ha n
  (twoColourCornerMulData_lastDot D Sc i j a ha n)
local notation "Dl" => heightTwoColourRightMul D Sc i j j a ha n
  (twoColourCornerMulData_appendDot D Sc i j a ha n)

/-- The comparison component of `Ind_j ⋙ Ind_i`, written on tensor products. -/
def heightTwoColourComparisonHom (M : HeightModules D Sc a ha n) :
    tensor Pc (tensor Qc M) ⟶ tensor T M :=
  (assoc Pc Qc M).inv ≫ whiskerRight (iso).hom M

/-- Its inverse, written on tensor products. -/
def heightTwoColourComparisonInv (M : HeightModules D Sc a ha n) :
    tensor T M ⟶ tensor Pc (tensor Qc M) :=
  whiskerRight (iso).inv M ≫ (assoc Pc Qc M).hom

end Transport

/-! ### The slides on the induction functors -/

section InductionSlides
variable {i j : I} (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "Hij" => heightTwoColourComparisonHom D Sc i j a ha n
local notation "Hji" => heightTwoColourComparisonHom D Sc j i a ha n
local notation "Iji" => heightTwoColourComparisonInv D Sc j i a ha n
local notation "Tij" => heightCompositionCorner D Sc i j a ha n
local notation "Tji" => heightCompositionCorner D Sc j i a ha n

end InductionSlides

end OddMath.QuiverHecke.CyclotomicAction
