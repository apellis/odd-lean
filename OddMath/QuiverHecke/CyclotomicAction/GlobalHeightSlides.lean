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

theorem svec_hom_ext_homogeneous {V W : SVec k} {f g : V ⟶ W}
    (h : ∀ (p : ZMod 2) (v : V), v ∈ V.part p → f v = g v) : f = g :=
  SVec.hom_ext fun v => by
    rw [← V.proj_apply_add v, SVec.hom_map_add, SVec.hom_map_add,
      h 0 _ (V.proj_mem_part 0 v), h 1 _ (V.proj_mem_part 1 v)]

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

theorem heightCompositionRightMul_parity {u : C} (hu : CornerMulData D Sc i a ha n u) :
    heightCompositionRightMul D Sc i a ha n hu ∈ parity (R := k) T T d :=
  SuperBimodule.mem_parity_iff.2 (heightCompositionRightMulLinear_parity D Sc i a ha n hu)

theorem heightCompositionRightMul_apply {u : C} (hu : CornerMulData D Sc i a ha n u)
    {p : ZMod 2} (x : (T).toSVec) (hx : x ∈ (T).toSVec.part p) :
    ((heightCompositionRightMul D Sc i a ha n hu).1 x).val = koszulSign p d • (x.val * u) := by
  change ((T).toSVec.sgn d x).val * u = _
  rw [SVec.sgn_apply_of_mem d hx]
  change (sign k (p * d) • x.val) * u = _
  rw [smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

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

theorem koszulSign_slide_aux₁ (p d : ZMod 2) :
    koszulSign (p + d) (d * d) * koszulSign p d = koszulSign d d := by
  revert p d; decide

theorem koszulSign_slide_aux₂ (p d : ZMod 2) :
    koszulSign (p + d * d) d * koszulSign p (d * d) = koszulSign d d := by
  revert p d; decide

section Additive
variable {a : I → _root_.Polynomial k} {ha : CyclotomicPolynomialParity D a} {m n : ℕ}

/-- Underlying linear maps of superbimodule morphisms, additively. -/
def heightBimodValHom (V W : SuperBimodule (heightParity D Sc a ha m) (heightParity D Sc a ha n)) :
    (V ⟶ W) →+ (V.toSVec ⟶ W.toSVec) where
  toFun f := f.1
  map_zero' := rfl
  map_add' f g := SuperBimodule.add_val f g

theorem heightBimod_sub_val {V W : SuperBimodule (heightParity D Sc a ha m)
    (heightParity D Sc a ha n)} (f g : V ⟶ W) : (f - g).1 = f.1 - g.1 :=
  map_sub (heightBimodValHom D Sc V W) f g

theorem heightBimod_zsmul_val {V W : SuperBimodule (heightParity D Sc a ha m)
    (heightParity D Sc a ha n)} (c : ℤ) (f : V ⟶ W) : (c • f).1 = c • f.1 :=
  map_zsmul (heightBimodValHom D Sc V W) c f

/-- Whiskering on the right by a module, additively. -/
def heightWhiskerRightHom {V W : SuperBimodule (heightParity D Sc a ha m)
    (heightParity D Sc a ha n)}
    (M : HeightModules D Sc a ha n) :
    (V ⟶ W) →+ (tensor V M ⟶ tensor W M) :=
  AddMonoidHom.mk' (fun f => whiskerRight f M) fun f g => add_whiskerRight f M g

theorem heightSub_zsmul_whiskerRight {V W : SuperBimodule (heightParity D Sc a ha m)
    (heightParity D Sc a ha n)}
    (M : HeightModules D Sc a ha n)
    (f g : V ⟶ W) (c : ℤ) :
    whiskerRight (f - c • g) M = whiskerRight f M - c • whiskerRight g M := by
  change heightWhiskerRightHom D Sc M (f - c • g) = _
  rw [map_sub, map_zsmul]
  rfl

theorem heightZsmul_whiskerRight {V W : SuperBimodule (heightParity D Sc a ha m)
    (heightParity D Sc a ha n)}
    (M : HeightModules D Sc a ha n)
    (f : V ⟶ W) (c : ℤ) : whiskerRight (c • f) M = c • whiskerRight f M :=
  map_zsmul (heightWhiskerRightHom D Sc M) c f

end Additive

/-! ### The slides on the corner -/

section CornerSlides
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "T" => heightCompositionCorner D Sc i i a ha n
local notation "d" => D.parity i
local notation "Dr" => heightCompositionRightMul D Sc i a ha n (cornerMulData_lastDot D Sc i a ha n)
local notation "Dl" => heightCompositionRightMul D Sc i a ha n (cornerMulData_appendDot D Sc i a ha n)
local notation "Cr" => heightCompositionSuperCrossing D Sc i i a ha n

private theorem rightMul_apply_mem {u : heightAlgebra D Sc a (n + 1 + 1)}
    (hu : CornerMulData D Sc i a ha n u) {p : ZMod 2} {z : (T).toSVec}
    (hz : z ∈ (T).toSVec.part p) :
    (heightCompositionRightMul D Sc i a ha n hu).1 z ∈ (T).toSVec.part (p + d) :=
  SVec.apply_mem_part (heightCompositionRightMulLinear_parity D Sc i a ha n hu) hz

private theorem crossing_apply_mem {p : ZMod 2} {z : (T).toSVec}
    (hz : z ∈ (T).toSVec.part p) :
    (Cr).1 z ∈ (T).toSVec.part (p + d * d) :=
  SVec.apply_mem_part (heightCompositionCrossingLinear_parity D Sc i i a ha n) hz

/-- **Left slide on the corner**: `ψ y₁ - s y₂ ψ = s` in diagrammatic order. -/
theorem heightCompositionCorner_slide_left :
    Cr ≫ Dl - koszulSign d d • (Dr ≫ Cr) = koszulSign d d • 𝟙 T := by
  apply SuperBimodule.hom_ext
  rw [heightBimod_sub_val, heightBimod_zsmul_val, heightBimod_zsmul_val,
    SuperBimodule.comp_val, SuperBimodule.comp_val, SuperBimodule.id_val]
  refine svec_hom_ext_homogeneous fun p z hz => Subtype.ext ?_
  simp only [SVec.sub_apply, SVec.zsmul_apply, SVec.comp_apply, SVec.id_apply]
  change ((Dl).1 ((Cr).1 z)).val - koszulSign d d • ((Cr).1 ((Dr).1 z)).val =
    koszulSign d d • z.val
  rw [heightCompositionRightMul_apply D Sc i a ha n _ _ (crossing_apply_mem D Sc i a ha n hz),
    heightCompositionSuperCrossing_apply D Sc i i a ha n _ hz,
    heightCompositionSuperCrossing_apply D Sc i i a ha n _
      (rightMul_apply_mem D Sc i a ha n _ hz),
    heightCompositionRightMul_apply D Sc i a ha n _ _ hz,
    smul_mul_assoc, smul_mul_assoc, smul_smul (koszulSign (p + d * d) d),
    smul_smul (koszulSign (p + d) (d * d)), koszulSign_slide_aux₁, koszulSign_slide_aux₂,
    koszulSign_smul_smul, mul_assoc, mul_assoc,
    ← koszulSign_smul_smul d d (z.val * (heightLastDot D Sc a i (n + 1) *
      heightLastCrossing D Sc a i i n)),
    ← smul_sub, ← mul_smul_comm, ← mul_sub, heightLastCrossing_slide_left]
  exact congrArg (koszulSign d d • ·) z.2

/-- **Right slide on the corner**: `y₁ ψ - s ψ y₂ = s` in diagrammatic order. -/
theorem heightCompositionCorner_slide_right :
    Dl ≫ Cr - koszulSign d d • (Cr ≫ Dr) = koszulSign d d • 𝟙 T := by
  apply SuperBimodule.hom_ext
  rw [heightBimod_sub_val, heightBimod_zsmul_val, heightBimod_zsmul_val,
    SuperBimodule.comp_val, SuperBimodule.comp_val, SuperBimodule.id_val]
  refine svec_hom_ext_homogeneous fun p z hz => Subtype.ext ?_
  simp only [SVec.sub_apply, SVec.zsmul_apply, SVec.comp_apply, SVec.id_apply]
  change ((Cr).1 ((Dl).1 z)).val - koszulSign d d • ((Dr).1 ((Cr).1 z)).val =
    koszulSign d d • z.val
  rw [heightCompositionSuperCrossing_apply D Sc i i a ha n _
      (rightMul_apply_mem D Sc i a ha n _ hz),
    heightCompositionRightMul_apply D Sc i a ha n _ _ hz,
    heightCompositionRightMul_apply D Sc i a ha n _ _ (crossing_apply_mem D Sc i a ha n hz),
    heightCompositionSuperCrossing_apply D Sc i i a ha n _ hz,
    smul_mul_assoc, smul_mul_assoc, smul_smul (koszulSign (p + d) (d * d)),
    smul_smul (koszulSign (p + d * d) d), koszulSign_slide_aux₁, koszulSign_slide_aux₂,
    koszulSign_smul_smul, mul_assoc, mul_assoc,
    ← koszulSign_smul_smul d d (z.val * (heightLastCrossing D Sc a i i n *
      heightLastDot D Sc a i (n + 1))),
    ← smul_sub, ← mul_smul_comm, ← mul_sub, heightLastCrossing_slide_right]
  exact congrArg (koszulSign d d • ·) z.2

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

/-- The outer dot becomes `y₂` on the corner. -/
theorem heightComposition_dot_outer :
    whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) Qc ≫ (iso).hom = (iso).hom ≫ Dr := by
  apply SuperBimodule.hom_ext
  rw [SuperBimodule.comp_val, SuperBimodule.comp_val]
  refine tensor_hom_ext_homogeneous Pc Qc fun p q x y hx hy => Subtype.ext ?_
  have hxy := SVec.apply_mem_part (SuperBimodule.mem_parity_iff.1
    (heightInductionCompositionIso_hom_mem D Sc i i a ha n)) (btmul_mem_part Pc Qc hx hy)
  rw [add_zero] at hxy
  have hc := heightLastDot_comm D Sc a i ha (n + 1)
    ((heightInductionCorner_mem_part_iff D Sc i a ha n).1 hy)
  rw [SVec.comp_apply, SVec.comp_apply, whiskerRight_btmul,
    heightCompositionRightMul_apply D Sc i a ha n _ _ hxy,
    heightInductionCompositionIso_hom_btmul, heightInductionCompositionIso_hom_btmul,
    heightInductionSuperDot_apply D Sc i a ha (n + 1) x hx, smul_mul_assoc, mul_assoc, mul_assoc,
    hc, mul_smul_comm, smul_smul, koszulSign_add_left, mul_assoc, koszulSign_mul_self, mul_one]

/-- The inner dot becomes `y₁` on the corner. -/
theorem heightComposition_dot_inner :
    whiskerLeft Pc (heightInductionSuperDot D Sc i a ha n) ≫ (iso).hom = (iso).hom ≫ Dl := by
  apply SuperBimodule.hom_ext
  rw [SuperBimodule.comp_val, SuperBimodule.comp_val]
  refine tensor_hom_ext_homogeneous Pc Qc fun p q x y hx hy => Subtype.ext ?_
  have hxy := SVec.apply_mem_part (SuperBimodule.mem_parity_iff.1
    (heightInductionCompositionIso_hom_mem D Sc i i a ha n)) (btmul_mem_part Pc Qc hx hy)
  rw [add_zero] at hxy
  rw [SVec.comp_apply, SVec.comp_apply,
    whiskerLeft_btmul Pc _ (heightInductionSuperDot_parity D Sc i a ha n) hx,
    heightCompositionRightMul_apply D Sc i a ha n _ _ hxy, heightInductionCompositionIso_hom_btmul,
    SVec.hom_map_smul]
  change sign k (p * d) • ((((iso).hom).1 (btmul Pc Qc x
    ((heightInductionSuperDot D Sc i a ha n).1 y))).1) = _
  rw [heightInductionCompositionIso_hom_btmul, heightInductionSuperDot_apply D Sc i a ha n y hy,
    map_zsmul, map_mul, mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, smul_smul,
    ← koszulSign_add_left, mul_assoc]

/-- The comparison component, written on tensor products. -/
def heightComparisonHom (M : HeightModules D Sc a ha n) : tensor Pc (tensor Qc M) ⟶ tensor T M :=
  (assoc Pc Qc M).inv ≫ whiskerRight (iso).hom M

/-- Its inverse, written on tensor products. -/
def heightComparisonInv (M : HeightModules D Sc a ha n) : tensor T M ⟶ tensor Pc (tensor Qc M) :=
  whiskerRight (iso).inv M ≫ (assoc Pc Qc M).hom

theorem heightComparisonHom_inv (M : HeightModules D Sc a ha n) :
    heightComparisonHom D Sc i a ha n M ≫ heightComparisonInv D Sc i a ha n M = 𝟙 _ := by
  rw [heightComparisonHom, heightComparisonInv, Category.assoc, ← Category.assoc
    (whiskerRight (iso).hom M), ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id]

theorem heightComparisonInv_hom (M : HeightModules D Sc a ha n) :
    heightComparisonInv D Sc i a ha n M ≫ heightComparisonHom D Sc i a ha n M = 𝟙 _ := by
  rw [heightComparisonHom, heightComparisonInv, Category.assoc, ← Category.assoc
    (assoc Pc Qc M).hom, Iso.hom_inv_id, Category.id_comp, ← comp_whiskerRight, Iso.inv_hom_id,
    id_whiskerRight]

/-- The outer dot whiskered by the inner induction, through the comparison. -/
theorem heightComparison_dot_outer_app (M : HeightModules D Sc a ha n) :
    whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) (tensor Qc M) ≫
        heightComparisonHom D Sc i a ha n M =
      heightComparisonHom D Sc i a ha n M ≫ whiskerRight Dr M := by
  have h := assoc_naturality_left Pc Qc M (heightInductionSuperDot D Sc i a ha (n + 1))
  have h' : whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) (tensor Qc M) ≫
      (assoc Pc Qc M).inv = (assoc Pc Qc M).inv ≫
        whiskerRight (whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) Qc) M := by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  rw [heightComparisonHom, ← Category.assoc, h', Category.assoc, ← comp_whiskerRight,
    heightComposition_dot_outer, comp_whiskerRight, Category.assoc]

/-- The inner dot under the outer induction, through the comparison. -/
theorem heightComparison_dot_inner_app (M : HeightModules D Sc a ha n) :
    whiskerLeft Pc (whiskerRight (heightInductionSuperDot D Sc i a ha n) M) ≫
        heightComparisonHom D Sc i a ha n M =
      heightComparisonHom D Sc i a ha n M ≫ whiskerRight Dl M := by
  have h := assoc_naturality_middle Pc Qc M (heightInductionSuperDot D Sc i a ha n)
  have h' : whiskerLeft Pc (whiskerRight (heightInductionSuperDot D Sc i a ha n) M) ≫
      (assoc Pc Qc M).inv = (assoc Pc Qc M).inv ≫
        whiskerRight (whiskerLeft Pc (heightInductionSuperDot D Sc i a ha n)) M := by
    rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]
  rw [heightComparisonHom, ← Category.assoc, h', Category.assoc, ← comp_whiskerRight,
    heightComposition_dot_inner, comp_whiskerRight, Category.assoc]

private theorem comparisonInv_conj (M : HeightModules D Sc a ha n)
    {X : tensor Pc (tensor Qc M) ⟶ tensor Pc (tensor Qc M)} {A : T ⟶ T}
    (h : X ≫ heightComparisonHom D Sc i a ha n M =
      heightComparisonHom D Sc i a ha n M ≫ whiskerRight A M) :
    heightComparisonInv D Sc i a ha n M ≫ X =
      whiskerRight A M ≫ heightComparisonInv D Sc i a ha n M := by
  calc heightComparisonInv D Sc i a ha n M ≫ X
      = heightComparisonInv D Sc i a ha n M ≫ X ≫ heightComparisonHom D Sc i a ha n M ≫
          heightComparisonInv D Sc i a ha n M := by
        rw [heightComparisonHom_inv, Category.comp_id]
    _ = (heightComparisonInv D Sc i a ha n M ≫ heightComparisonHom D Sc i a ha n M) ≫
          whiskerRight A M ≫ heightComparisonInv D Sc i a ha n M := by
        rw [← Category.assoc X, h]
        simp only [Category.assoc]
    _ = whiskerRight A M ≫ heightComparisonInv D Sc i a ha n M := by
        rw [heightComparisonInv_hom, Category.id_comp]

/-- The two slides on the tensor products, from the corner slides. -/
private theorem comparison_slide (M : HeightModules D Sc a ha n)
    {X₁ X₂ : tensor Pc (tensor Qc M) ⟶ tensor Pc (tensor Qc M)} {A B C : T ⟶ T} (c : ℤ)
    (h₁ : X₁ ≫ heightComparisonHom D Sc i a ha n M =
      heightComparisonHom D Sc i a ha n M ≫ whiskerRight A M)
    (h₂ : X₂ ≫ heightComparisonHom D Sc i a ha n M =
      heightComparisonHom D Sc i a ha n M ≫ whiskerRight B M)
    (hC : C ≫ A - c • (B ≫ C) = c • 𝟙 T) :
    (heightComparisonHom D Sc i a ha n M ≫ whiskerRight C M ≫
        heightComparisonInv D Sc i a ha n M) ≫ X₁ -
      c • (X₂ ≫ heightComparisonHom D Sc i a ha n M ≫ whiskerRight C M ≫
        heightComparisonInv D Sc i a ha n M) = c • 𝟙 _ := by
  rw [Category.assoc, Category.assoc, comparisonInv_conj D Sc i a ha n M h₁,
    ← Category.assoc X₂, h₂]
  simp only [Category.assoc]
  rw [← Category.assoc (whiskerRight C M) (whiskerRight A M), ← comp_whiskerRight,
    ← Category.assoc (whiskerRight B M) (whiskerRight C M), ← comp_whiskerRight,
    ← Preadditive.comp_zsmul,
    ← Preadditive.zsmul_comp, ← Preadditive.comp_sub, ← Preadditive.sub_comp,
    ← heightSub_zsmul_whiskerRight, hC, heightZsmul_whiskerRight, id_whiskerRight,
    Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul, heightComparisonHom_inv]

/-- The right-hand analogue of `comparison_slide`. -/
private theorem comparison_slide' (M : HeightModules D Sc a ha n)
    {X₁ X₂ : tensor Pc (tensor Qc M) ⟶ tensor Pc (tensor Qc M)} {A B C : T ⟶ T} (c : ℤ)
    (h₁ : X₁ ≫ heightComparisonHom D Sc i a ha n M =
      heightComparisonHom D Sc i a ha n M ≫ whiskerRight A M)
    (h₂ : X₂ ≫ heightComparisonHom D Sc i a ha n M =
      heightComparisonHom D Sc i a ha n M ≫ whiskerRight B M)
    (hC : A ≫ C - c • (C ≫ B) = c • 𝟙 T) :
    X₁ ≫ heightComparisonHom D Sc i a ha n M ≫ whiskerRight C M ≫
        heightComparisonInv D Sc i a ha n M -
      c • ((heightComparisonHom D Sc i a ha n M ≫ whiskerRight C M ≫
        heightComparisonInv D Sc i a ha n M) ≫ X₂) = c • 𝟙 _ := by
  rw [Category.assoc, Category.assoc, comparisonInv_conj D Sc i a ha n M h₂,
    ← Category.assoc X₁, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc (whiskerRight A M) (whiskerRight C M), ← comp_whiskerRight,
    ← Category.assoc (whiskerRight C M) (whiskerRight B M), ← comp_whiskerRight,
    ← Preadditive.comp_zsmul,
    ← Preadditive.zsmul_comp, ← Preadditive.comp_sub, ← Preadditive.sub_comp,
    ← heightSub_zsmul_whiskerRight, hC, heightZsmul_whiskerRight, id_whiskerRight,
    Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul, heightComparisonHom_inv]

/-- **The left slide for two inductions of colour `i`** (components): with `ψ` the crossing,
`x₁` the inner and `x₂` the outer dot, `ψ x₁ - s x₂ ψ = s` in diagrammatic order. -/
theorem heightInduction_slide_left (M : HeightModules D Sc a ha n) :
    ((heightSuperInductionCrossing D Sc i i a ha n).app (d * d) M ≫
        (heightSuperInduction D Sc i a ha (n + 1)).map
          ((heightSuperInductionDot D Sc i a ha n).app d M) :
        (heightSuperInduction D Sc i a ha (n + 1)).obj ((heightSuperInduction D Sc i a ha n).obj M) ⟶
          (heightSuperInduction D Sc i a ha (n + 1)).obj
            ((heightSuperInduction D Sc i a ha n).obj M)) -
      koszulSign d d •
        ((heightSuperInductionDot D Sc i a ha (n + 1)).app d
            ((heightSuperInduction D Sc i a ha n).obj M) ≫
          (heightSuperInductionCrossing D Sc i i a ha n).app (d * d) M :
        (heightSuperInduction D Sc i a ha (n + 1)).obj ((heightSuperInduction D Sc i a ha n).obj M) ⟶
          (heightSuperInduction D Sc i a ha (n + 1)).obj
            ((heightSuperInduction D Sc i a ha n).obj M)) =
      koszulSign d d • 𝟙 _ := by
  have hX₁ : (heightSuperInductionDot D Sc i a ha n).app d M =
      whiskerRight (heightInductionSuperDot D Sc i a ha n) M := by
    simp only [heightSuperInductionDot, ↓reduceIte]
  have hX₂ : (heightSuperInductionDot D Sc i a ha (n + 1)).app d
      ((heightSuperInduction D Sc i a ha n).obj M) =
      whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) (tensor Qc M) := by
    simp only [heightSuperInductionDot, ↓reduceIte]; rfl
  rw [heightSuperInductionCrossing_app, hX₁, hX₂]
  exact comparison_slide D Sc i a ha n M _ (heightComparison_dot_inner_app D Sc i a ha n M)
    (heightComparison_dot_outer_app D Sc i a ha n M) (heightCompositionCorner_slide_left D Sc i a ha n)

/-- **The right slide for two inductions of colour `i`** (components):
`x₁ ψ - s ψ x₂ = s` in diagrammatic order. -/
theorem heightInduction_slide_right (M : HeightModules D Sc a ha n) :
    ((heightSuperInduction D Sc i a ha (n + 1)).map
          ((heightSuperInductionDot D Sc i a ha n).app d M) ≫
        (heightSuperInductionCrossing D Sc i i a ha n).app (d * d) M :
        (heightSuperInduction D Sc i a ha (n + 1)).obj ((heightSuperInduction D Sc i a ha n).obj M) ⟶
          (heightSuperInduction D Sc i a ha (n + 1)).obj
            ((heightSuperInduction D Sc i a ha n).obj M)) -
      koszulSign d d •
        ((heightSuperInductionCrossing D Sc i i a ha n).app (d * d) M ≫
          (heightSuperInductionDot D Sc i a ha (n + 1)).app d
            ((heightSuperInduction D Sc i a ha n).obj M) :
        (heightSuperInduction D Sc i a ha (n + 1)).obj ((heightSuperInduction D Sc i a ha n).obj M) ⟶
          (heightSuperInduction D Sc i a ha (n + 1)).obj
            ((heightSuperInduction D Sc i a ha n).obj M)) =
      koszulSign d d • 𝟙 _ := by
  have hX₁ : (heightSuperInductionDot D Sc i a ha n).app d M =
      whiskerRight (heightInductionSuperDot D Sc i a ha n) M := by
    simp only [heightSuperInductionDot, ↓reduceIte]
  have hX₂ : (heightSuperInductionDot D Sc i a ha (n + 1)).app d
      ((heightSuperInduction D Sc i a ha n).obj M) =
      whiskerRight (heightInductionSuperDot D Sc i a ha (n + 1)) (tensor Qc M) := by
    simp only [heightSuperInductionDot, ↓reduceIte]; rfl
  rw [heightSuperInductionCrossing_app, hX₁, hX₂]
  exact comparison_slide' D Sc i a ha n M _ (heightComparison_dot_inner_app D Sc i a ha n M)
    (heightComparison_dot_outer_app D Sc i a ha n M)
    (heightCompositionCorner_slide_right D Sc i a ha n)

end Transport

end OddMath.QuiverHecke.CyclotomicAction
