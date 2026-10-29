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

theorem heightTwoColourRightMul_parity {u : C} (hu : TwoColourCornerMulData D Sc i j c a ha n u) :
    heightTwoColourRightMul D Sc i j c a ha n hu ∈ parity (R := k) T T d :=
  SuperBimodule.mem_parity_iff.2 (heightTwoColourRightMulLinear_parity D Sc i j c a ha n hu)

theorem heightTwoColourRightMul_apply {u : C} (hu : TwoColourCornerMulData D Sc i j c a ha n u)
    {p : ZMod 2} (x : (T).toSVec) (hx : x ∈ (T).toSVec.part p) :
    ((heightTwoColourRightMul D Sc i j c a ha n hu).1 x).val = koszulSign p d • (x.val * u) := by
  change ((T).toSVec.sgn d x).val * u = _
  rw [SVec.sgn_apply_of_mem d hx]
  change (sign k (p * d) • x.val) * u = _
  rw [smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

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

/-- **Left slide on the corners**, distinct colours: `y_i ψ = ε ψ φⱼ(y_i)` in diagrammatic
order. -/
theorem heightCompositionCorner_slide_left_ne : Dr ≫ Cr = ε • (Cr ≫ Dl) := by
  apply SuperBimodule.hom_ext
  rw [heightBimod_zsmul_val, SuperBimodule.comp_val, SuperBimodule.comp_val]
  refine svec_hom_ext_homogeneous fun p z hz => Subtype.ext ?_
  simp only [SVec.zsmul_apply, SVec.comp_apply]
  have hz₁ : (Dr).1 z ∈ (heightCompositionCorner D Sc i j a ha n).toSVec.part
      (p + D.parity i) :=
    SVec.apply_mem_part (heightTwoColourRightMulLinear_parity D Sc i j i a ha n
      (twoColourCornerMulData_lastDot D Sc i j a ha n)) hz
  have hz₂ : (Cr).1 z ∈ (heightCompositionCorner D Sc j i a ha n).toSVec.part (p + d) :=
    SVec.apply_mem_part (heightCompositionCrossingLinear_parity D Sc i j a ha n) hz
  change ((Cr).1 ((Dr).1 z)).val = ε • ((Dl).1 ((Cr).1 z)).val
  rw [heightCompositionSuperCrossing_apply D Sc i j a ha n _ hz₁,
    heightTwoColourRightMul_apply D Sc i j i a ha n _ _ hz,
    heightTwoColourRightMul_apply D Sc j i i a ha n _ _ hz₂,
    heightCompositionSuperCrossing_apply D Sc i j a ha n _ hz]
  simp only [smul_mul_assoc, smul_smul, mul_assoc]
  rw [heightLastCrossing_slide_left_ne D Sc a hij n, ← zsmul_koszulSign_eq_zsign_smul (k := k)]
  simp only [mul_smul_comm, smul_smul]
  congr 1
  clear hz hz₁ hz₂
  generalize D.parity i = e
  generalize D.parity j = f
  revert p e f; decide

/-- **Right slide on the corners**, distinct colours: `ψ y_j = ε φᵢ(y_j) ψ` in diagrammatic
order. -/
theorem heightCompositionCorner_slide_right_ne : Cr ≫ Er = ε • (El ≫ Cr) := by
  apply SuperBimodule.hom_ext
  rw [heightBimod_zsmul_val, SuperBimodule.comp_val, SuperBimodule.comp_val]
  refine svec_hom_ext_homogeneous fun p z hz => Subtype.ext ?_
  simp only [SVec.zsmul_apply, SVec.comp_apply]
  have hz₁ : (El).1 z ∈ (heightCompositionCorner D Sc i j a ha n).toSVec.part
      (p + D.parity j) :=
    SVec.apply_mem_part (heightTwoColourRightMulLinear_parity D Sc i j j a ha n
      (twoColourCornerMulData_appendDot D Sc i j a ha n)) hz
  have hz₂ : (Cr).1 z ∈ (heightCompositionCorner D Sc j i a ha n).toSVec.part (p + d) :=
    SVec.apply_mem_part (heightCompositionCrossingLinear_parity D Sc i j a ha n) hz
  change ((Er).1 ((Cr).1 z)).val = ε • ((Cr).1 ((El).1 z)).val
  rw [heightCompositionSuperCrossing_apply D Sc i j a ha n _ hz₁,
    heightTwoColourRightMul_apply D Sc i j j a ha n _ _ hz,
    heightTwoColourRightMul_apply D Sc j i j a ha n _ _ hz₂,
    heightCompositionSuperCrossing_apply D Sc i j a ha n _ hz]
  simp only [smul_mul_assoc, smul_smul, mul_assoc]
  rw [heightLastCrossing_slide_right_ne D Sc a hij n, ← zsmul_koszulSign_eq_zsign_smul (k := k)]
  simp only [mul_smul_comm, smul_smul]
  congr 1
  clear hz hz₁ hz₂
  generalize D.parity i = e
  generalize D.parity j = f
  revert p e f; decide

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

/-- The outer dot becomes `y_i` on the two-colour corner. -/
theorem heightTwoColourComposition_dot_outer :
    whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) Qc ≫ (iso).hom =
      (iso).hom ≫ Dr := by
  apply SuperBimodule.hom_ext
  rw [SuperBimodule.comp_val, SuperBimodule.comp_val]
  refine tensor_hom_ext_homogeneous Pc Qc fun p q x y hx hy => Subtype.ext ?_
  have hxy := SVec.apply_mem_part (SuperBimodule.mem_parity_iff.1
    (heightInductionCompositionIso_hom_mem D Sc i j a ha n)) (btmul_mem_part Pc Qc hx hy)
  rw [add_zero] at hxy
  have hc := heightLastDot_comm D Sc a i ha (n + 1)
    ((heightInductionCorner_mem_part_iff D Sc j a ha n).1 hy)
  rw [SVec.comp_apply, SVec.comp_apply, whiskerRight_btmul,
    heightTwoColourRightMul_apply D Sc i j i a ha n _ _ hxy,
    heightInductionCompositionIso_hom_btmul, heightInductionCompositionIso_hom_btmul,
    heightInductionSuperDot_apply D Sc i a ha (n + 1) x hx, smul_mul_assoc, mul_assoc, mul_assoc,
    hc, mul_smul_comm, smul_smul, koszulSign_add_left, mul_assoc, koszulSign_mul_self, mul_one]

/-- The inner dot becomes `φᵢ(y_j)` on the two-colour corner. -/
theorem heightTwoColourComposition_dot_inner :
    whiskerLeft Pc (heightInductionSuperDot D Sc j a ha n) ≫ (iso).hom = (iso).hom ≫ Dl := by
  apply SuperBimodule.hom_ext
  rw [SuperBimodule.comp_val, SuperBimodule.comp_val]
  refine tensor_hom_ext_homogeneous Pc Qc fun p q x y hx hy => Subtype.ext ?_
  have hxy := SVec.apply_mem_part (SuperBimodule.mem_parity_iff.1
    (heightInductionCompositionIso_hom_mem D Sc i j a ha n)) (btmul_mem_part Pc Qc hx hy)
  rw [add_zero] at hxy
  rw [SVec.comp_apply, SVec.comp_apply,
    whiskerLeft_btmul Pc _ (heightInductionSuperDot_parity D Sc j a ha n) hx,
    heightTwoColourRightMul_apply D Sc i j j a ha n _ _ hxy,
    heightInductionCompositionIso_hom_btmul, SVec.hom_map_smul]
  change sign k (p * D.parity j) • ((((iso).hom).1 (btmul Pc Qc x
    ((heightInductionSuperDot D Sc j a ha n).1 y))).1) = _
  rw [heightInductionCompositionIso_hom_btmul, heightInductionSuperDot_apply D Sc j a ha n y hy,
    map_zsmul, map_mul, mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, smul_smul,
    ← koszulSign_add_left, mul_assoc]

/-- The comparison component of `Ind_j ⋙ Ind_i`, written on tensor products. -/
def heightTwoColourComparisonHom (M : HeightModules D Sc a ha n) :
    tensor Pc (tensor Qc M) ⟶ tensor T M :=
  (assoc Pc Qc M).inv ≫ whiskerRight (iso).hom M

/-- Its inverse, written on tensor products. -/
def heightTwoColourComparisonInv (M : HeightModules D Sc a ha n) :
    tensor T M ⟶ tensor Pc (tensor Qc M) :=
  whiskerRight (iso).inv M ≫ (assoc Pc Qc M).hom

theorem heightTwoColourComparisonHom_inv (M : HeightModules D Sc a ha n) :
    heightTwoColourComparisonHom D Sc i j a ha n M ≫
      heightTwoColourComparisonInv D Sc i j a ha n M = 𝟙 _ := by
  rw [heightTwoColourComparisonHom, heightTwoColourComparisonInv, Category.assoc,
    ← Category.assoc (whiskerRight (iso).hom M), ← comp_whiskerRight, Iso.hom_inv_id,
    id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

theorem heightTwoColourComparisonInv_hom (M : HeightModules D Sc a ha n) :
    heightTwoColourComparisonInv D Sc i j a ha n M ≫
      heightTwoColourComparisonHom D Sc i j a ha n M = 𝟙 _ := by
  rw [heightTwoColourComparisonHom, heightTwoColourComparisonInv, Category.assoc,
    ← Category.assoc (assoc Pc Qc M).hom, Iso.hom_inv_id, Category.id_comp,
    ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]

/-- The outer dot whiskered by the inner induction, through the comparison. -/
theorem heightTwoColourComparison_dot_outer_app (M : HeightModules D Sc a ha n) :
    whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) (tensor Qc M) ≫
        heightTwoColourComparisonHom D Sc i j a ha n M =
      heightTwoColourComparisonHom D Sc i j a ha n M ≫ whiskerRight Dr M := by
  have h := assoc_naturality_left Pc Qc M (heightInductionSuperDot D Sc i a ha (n + 1))
  have h' : whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) (tensor Qc M) ≫
      (assoc Pc Qc M).inv = (assoc Pc Qc M).inv ≫
        whiskerRight (whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) Qc) M := by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  rw [heightTwoColourComparisonHom, ← Category.assoc, h', Category.assoc, ← comp_whiskerRight,
    heightTwoColourComposition_dot_outer, comp_whiskerRight, Category.assoc]

/-- The inner dot under the outer induction, through the comparison. -/
theorem heightTwoColourComparison_dot_inner_app (M : HeightModules D Sc a ha n) :
    whiskerLeft Pc (whiskerRight (heightInductionSuperDot D Sc j a ha n) M) ≫
        heightTwoColourComparisonHom D Sc i j a ha n M =
      heightTwoColourComparisonHom D Sc i j a ha n M ≫ whiskerRight Dl M := by
  have h := assoc_naturality_middle Pc Qc M (heightInductionSuperDot D Sc j a ha n)
  have h' : whiskerLeft Pc (whiskerRight (heightInductionSuperDot D Sc j a ha n) M) ≫
      (assoc Pc Qc M).inv = (assoc Pc Qc M).inv ≫
        whiskerRight (whiskerLeft Pc (heightInductionSuperDot D Sc j a ha n)) M := by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  rw [heightTwoColourComparisonHom, ← Category.assoc, h', Category.assoc, ← comp_whiskerRight,
    heightTwoColourComposition_dot_inner, comp_whiskerRight, Category.assoc]

theorem heightTwoColourComparisonInv_conj (M : HeightModules D Sc a ha n)
    {X : tensor Pc (tensor Qc M) ⟶ tensor Pc (tensor Qc M)} {A : T ⟶ T}
    (h : X ≫ heightTwoColourComparisonHom D Sc i j a ha n M =
      heightTwoColourComparisonHom D Sc i j a ha n M ≫ whiskerRight A M) :
    heightTwoColourComparisonInv D Sc i j a ha n M ≫ X =
      whiskerRight A M ≫ heightTwoColourComparisonInv D Sc i j a ha n M := by
  calc heightTwoColourComparisonInv D Sc i j a ha n M ≫ X
      = heightTwoColourComparisonInv D Sc i j a ha n M ≫ X ≫
          heightTwoColourComparisonHom D Sc i j a ha n M ≫
            heightTwoColourComparisonInv D Sc i j a ha n M := by
        rw [heightTwoColourComparisonHom_inv, Category.comp_id]
    _ = (heightTwoColourComparisonInv D Sc i j a ha n M ≫
            heightTwoColourComparisonHom D Sc i j a ha n M) ≫
          whiskerRight A M ≫ heightTwoColourComparisonInv D Sc i j a ha n M := by
        rw [← Category.assoc X, h]
        simp only [Category.assoc]
    _ = whiskerRight A M ≫ heightTwoColourComparisonInv D Sc i j a ha n M := by
        rw [heightTwoColourComparisonInv_hom, Category.id_comp]

end Transport

/-! ### The slides on the induction functors -/

section InductionSlides
variable {i j : I} (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "Hij" => heightTwoColourComparisonHom D Sc i j a ha n
local notation "Hji" => heightTwoColourComparisonHom D Sc j i a ha n
local notation "Iji" => heightTwoColourComparisonInv D Sc j i a ha n
local notation "Tij" => heightCompositionCorner D Sc i j a ha n
local notation "Tji" => heightCompositionCorner D Sc j i a ha n

private theorem twoColour_comparison_slide_left (M : HeightModules D Sc a ha n)
    {X₂ X₁ : _} {A : Tij ⟶ Tij} {B : Tji ⟶ Tji} {C : Tij ⟶ Tji}
    (c : ℤ) (h₂ : X₂ ≫ Hij M = Hij M ≫ whiskerRight A M)
    (h₁ : X₁ ≫ Hji M = Hji M ≫ whiskerRight B M) (hC : A ≫ C = c • (C ≫ B)) :
    X₂ ≫ Hij M ≫ whiskerRight C M ≫ Iji M = c • ((Hij M ≫ whiskerRight C M ≫ Iji M) ≫ X₁) := by
  rw [Category.assoc, Category.assoc,
    heightTwoColourComparisonInv_conj D Sc j i a ha n M h₁, ← Category.assoc X₂, h₂,
    Category.assoc, ← Category.assoc (whiskerRight A M), ← comp_whiskerRight, hC,
    heightZsmul_whiskerRight, comp_whiskerRight, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  simp only [Category.assoc]

private theorem twoColour_comparison_slide_right (M : HeightModules D Sc a ha n)
    {X₂ X₁ : _} {A : Tij ⟶ Tij} {B : Tji ⟶ Tji} {C : Tij ⟶ Tji}
    (c : ℤ) (h₁ : X₁ ≫ Hij M = Hij M ≫ whiskerRight A M)
    (h₂ : X₂ ≫ Hji M = Hji M ≫ whiskerRight B M) (hC : C ≫ B = c • (A ≫ C)) :
    (Hij M ≫ whiskerRight C M ≫ Iji M) ≫ X₂ = c • (X₁ ≫ Hij M ≫ whiskerRight C M ≫ Iji M) := by
  rw [Category.assoc, Category.assoc,
    heightTwoColourComparisonInv_conj D Sc j i a ha n M h₂, ← Category.assoc X₁, h₁,
    Category.assoc, ← Category.assoc (whiskerRight C M), ← comp_whiskerRight, hC,
    heightZsmul_whiskerRight, comp_whiskerRight, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  simp only [Category.assoc]

/-- **The left slide for two inductions of distinct colours** (components): with `ψ` the
crossing `Ind_j ⋙ Ind_i ⟶ Ind_i ⋙ Ind_j`, the outer dot of colour `i` followed by `ψ` is
`ε` times `ψ` followed by the inner dot of colour `i`, `ε = (-1)^{|i||j|}`. -/
theorem heightInduction_slide_left_ne (hij : i ≠ j) (M : HeightModules D Sc a ha n) :
    (heightSuperInductionDot D Sc i a ha (n + 1)).app (D.parity i)
          ((heightSuperInduction D Sc j a ha n).obj M) ≫
        (heightSuperInductionCrossing D Sc i j a ha n).app (D.parity i * D.parity j) M =
      koszulSign (D.parity i) (D.parity j) •
        ((heightSuperInductionCrossing D Sc i j a ha n).app (D.parity i * D.parity j) M ≫
          (heightSuperInduction D Sc j a ha (n + 1)).map
            ((heightSuperInductionDot D Sc i a ha n).app (D.parity i) M)) := by
  have hX₁ : (heightSuperInductionDot D Sc i a ha n).app (D.parity i) M =
      whiskerRight (heightInductionSuperDot D Sc i a ha n) M := by
    simp only [heightSuperInductionDot, ↓reduceIte]
  have hX₂ : (heightSuperInductionDot D Sc i a ha (n + 1)).app (D.parity i)
      ((heightSuperInduction D Sc j a ha n).obj M) =
      whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1))
        (tensor (heightInductionCorner D Sc j a ha n) M) := by
    simp only [heightSuperInductionDot, ↓reduceIte]; rfl
  rw [heightSuperInductionCrossing_app, hX₁, hX₂]
  exact twoColour_comparison_slide_left D Sc a ha n M _
    (heightTwoColourComparison_dot_outer_app D Sc i j a ha n M)
    (heightTwoColourComparison_dot_inner_app D Sc j i a ha n M)
    (heightCompositionCorner_slide_left_ne D Sc hij a ha n)

/-- **The right slide for two inductions of distinct colours** (components): `ψ` followed by
the outer dot of colour `j` is `ε` times the inner dot of colour `j` followed by `ψ`. -/
theorem heightInduction_slide_right_ne (hij : i ≠ j) (M : HeightModules D Sc a ha n) :
    (heightSuperInductionCrossing D Sc i j a ha n).app (D.parity i * D.parity j) M ≫
        (heightSuperInductionDot D Sc j a ha (n + 1)).app (D.parity j)
          ((heightSuperInduction D Sc i a ha n).obj M) =
      koszulSign (D.parity i) (D.parity j) •
        ((heightSuperInduction D Sc i a ha (n + 1)).map
            ((heightSuperInductionDot D Sc j a ha n).app (D.parity j) M) ≫
          (heightSuperInductionCrossing D Sc i j a ha n).app (D.parity i * D.parity j) M) := by
  have hX₁ : (heightSuperInductionDot D Sc j a ha n).app (D.parity j) M =
      whiskerRight (heightInductionSuperDot D Sc j a ha n) M := by
    simp only [heightSuperInductionDot, ↓reduceIte]
  have hX₂ : (heightSuperInductionDot D Sc j a ha (n + 1)).app (D.parity j)
      ((heightSuperInduction D Sc i a ha n).obj M) =
      whiskerRight (heightInductionSuperDot D Sc j a ha (n + 1))
        (tensor (heightInductionCorner D Sc i a ha n) M) := by
    simp only [heightSuperInductionDot, ↓reduceIte]; rfl
  rw [heightSuperInductionCrossing_app, hX₁, hX₂]
  exact twoColour_comparison_slide_right D Sc a ha n M _
    (heightTwoColourComparison_dot_inner_app D Sc i j a ha n M)
    (heightTwoColourComparison_dot_outer_app D Sc j i a ha n M)
    (heightCompositionCorner_slide_right_ne D Sc hij a ha n)

end InductionSlides

end OddMath.QuiverHecke.CyclotomicAction
