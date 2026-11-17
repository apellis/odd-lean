import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight.GlobalHeightCrossing
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Global height

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# The dot on induction at every height and on global content blocks

Supports the dot of `Categorification/KLR/CyclotomicAction/Global.lean`
(`globalDot`). `heightLastDot` is the last dot of the extended tower: at one
strand it is the image of `affineLastDot` in the height-one quotient, and at
positive height it is `cyclotomicLastDot`. The signed-left corner map
`x ↦ (-1)^{|i||x|} x c` of `SuperDot` is restated along `heightAppend`, giving
`heightSuperInductionDot`, homogeneous of parity `|i|` (odd colours get the
odd dot). It restricts to content blocks and transports to the global content
categories (`globalContentDot`).
-/

noncomputable section
open CategoryTheory StringDiagrams
open Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section LastDot
variable (a : I → _root_.Polynomial k) (i : I)

/-- The last dot of the extended tower, in the algebra one strand up. -/
def heightLastDot : (n : ℕ) → heightAlgebra D Sc a (n + 1)
  | 0 => cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0)
  | n + 1 => cyclotomicLastDot D Sc i a n

theorem heightLastDot_parity (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    heightLastDot D Sc a i n ∈ heightParity D Sc a ha (n + 1) (D.parity i) := by
  cases n with
  | zero => exact cyclotomicMk_parity D Sc a ha 0 (affineLastDot_parity D Sc i 0)
  | succ n => exact cyclotomicLastDot_parity D Sc i a ha n

theorem heightLastDot_comm (ha : CyclotomicPolynomialParity D a) (n : ℕ) {p : ZMod 2}
    {r : heightAlgebra D Sc a n} (hr : r ∈ heightParity D Sc a ha n p) :
    heightAppend D Sc a i n r * heightLastDot D Sc a i n =
      Supercategory.koszulSign p (D.parity i) •
        (heightLastDot D Sc a i n * heightAppend D Sc a i n r) := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 r) *
      cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) =
      Supercategory.koszulSign p (D.parity i) •
        (cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) *
          cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 r))
    rw [← map_mul, ← map_mul, ← map_zsmul]
    exact congrArg (cyclotomicMk D Sc a 0) (affineLastDot_comm D Sc i 0 hr)
  | succ n => exact cyclotomicLastDot_comm D Sc i a ha n hr

theorem heightLastDot_corner (n : ℕ) :
    heightAppend D Sc a i n 1 * heightLastDot D Sc a i n = heightLastDot D Sc a i n ∧
    heightLastDot D Sc a i n * heightAppend D Sc a i n 1 = heightLastDot D Sc a i n := by
  cases n with
  | zero =>
    change cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 1) *
        cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) =
        cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) ∧
      cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0) *
        cyclotomicMk D Sc a 0 (appendAlgebra D Sc i 0 1) =
        cyclotomicMk D Sc a 0 (affineLastDot D Sc i 0)
    rw [← map_mul, ← map_mul, append_one_mul_affineLastDot, affineLastDot_mul_append_one]
    exact ⟨rfl, rfl⟩
  | succ n => exact cyclotomicLastDot_corner D Sc i a n

end LastDot

variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "P" => heightInductionCorner D Sc i a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "c" => heightLastDot D Sc a i n
local notation "d" => D.parity i

private theorem height_dot_mul_mem (x : heightAlgebra D Sc a (n + 1))
    (_hx : x ∈ heightInductionCornerSubmodule D Sc i a n) :
    x * c ∈ heightInductionCornerSubmodule D Sc i a n := by
  change (x * c) * heightAppend D Sc a i n 1 = x * c
  rw [mul_assoc, (heightLastDot_corner D Sc a i n).2]

/-- The parity sign followed by right multiplication by the last dot. -/
def heightInductionDotLinear : (P).toSVec ⟶ (P).toSVec :=
  SVec.ofHom ((P).toSVec.sgn d) ≫
    SVec.restrictHom ((SuperBimodule.regular GB).ract c) (height_dot_mul_mem D Sc i a n)

/-- The dot has the parity of the induction colour. -/
theorem heightInductionDotLinear_parity :
    heightInductionDotLinear D Sc i a ha n ∈ SVec.parityHom (P).toSVec (P).toSVec d := by
  change heightInductionDotLinear D Sc i a ha n ∈ parity (R := k) (P).toSVec (P).toSVec d
  unfold heightInductionDotLinear
  have hd := SVec.restrictHom_mem (hU := heightInductionCorner_odd_mem D Sc i a ha n)
    (hU' := heightInductionCorner_odd_mem D Sc i a ha n)
    ((SuperBimodule.regular GB).ract_mem d c
      (heightLastDot_parity D Sc a i ha n)) (height_dot_mul_mem D Sc i a n)
  simpa only [heightInductionCorner, heightInductionCornerSpace, SuperBimodule.regular, zero_add] using
    Supercategory.comp_mem (SVec.sgn_mem (P).toSVec d) hd

private theorem height_sgn_action {p : ZMod 2} {f : (P).toSVec ⟶ (P).toSVec}
    (hf : f ∈ SVec.parityHom (P).toSVec (P).toSVec p) (x : (P).toSVec) :
    (P).toSVec.sgn d (f x) = sign k (p * d) • f ((P).toSVec.sgn d x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf d) x

/-- Signed left linearity and ordinary right linearity use the concrete last-dot slide. -/
theorem heightInductionDotLinear_isHom :
    SuperBimodule.IsHom P P (heightInductionDotLinear D Sc i a ha n) := by
  apply (SuperBimodule.isHom_iff_of_mem (heightInductionDotLinear_parity D Sc i a ha n)).2
  constructor
  · intro p b hb
    apply SVec.hom_ext
    intro x
    have h := height_sgn_action D Sc i a ha n ((P).lact_mem p b hb) x
    apply Subtype.ext
    change ((P).toSVec.sgn d ((P).lact b x)).val * c =
      sign k (p * d) • (b * (((P).toSVec.sgn d x).val * c))
    rw [h]
    change (sign k (p * d) • (b * ((P).toSVec.sgn d x).val)) * c = _
    rw [smul_mul_assoc, mul_assoc]
  · intro r
    induction r using SuperBimodule.alg_induction_on GA with
    | zero => simp
    | add r s hr hs => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hr, hs]
    | hom p r hr =>
      apply SVec.hom_ext
      intro x
      have h := height_sgn_action D Sc i a ha n ((P).ract_mem p r hr) x
      apply Subtype.ext
      change ((P).toSVec.sgn d ((P).ract r x)).val * c =
        (((P).toSVec.sgn d x).val * c) * heightAppend D Sc a i n r
      rw [h]
      change (sign k (p * d) • (((P).toSVec.sgn d x).val *
        heightAppend D Sc a i n r)) * c = _
      rw [smul_mul_assoc, mul_assoc, heightLastDot_comm D Sc a i ha n hr,
        mul_smul_comm, Supercategory.sign_mul, Int.cast_smul_eq_zsmul, koszulSign_smul_smul, mul_assoc]

/-- The homogeneous dot endomorphism of the induction corner at every height. -/
def heightInductionSuperDot : P ⟶ P :=
  ⟨heightInductionDotLinear D Sc i a ha n, heightInductionDotLinear_isHom D Sc i a ha n⟩

theorem heightInductionSuperDot_parity :
    heightInductionSuperDot D Sc i a ha n ∈ parity (R := k) P P d :=
  SuperBimodule.mem_parity_iff.2 (heightInductionDotLinear_parity D Sc i a ha n)

/-- The last dot as a supernatural endomorphism of balanced-tensor induction. -/
def heightSuperInductionDot :
    SuperNatTrans k (heightSuperInduction D Sc i a ha n)
      (heightSuperInduction D Sc i a ha n) where
  app p M := if p = d then SuperBimodule.whiskerRight (heightInductionSuperDot D Sc i a ha n) M else 0
  app_mem p M := by
    split_ifs with h
    · subst p
      exact SuperBimodule.whiskerRight_mem P (heightInductionSuperDot_parity D Sc i a ha n) M
    · exact Submodule.zero_mem _
  naturality p M N q f hf := by
    change SuperBimodule.whiskerLeft P f ≫ (if p = d then
        SuperBimodule.whiskerRight (heightInductionSuperDot D Sc i a ha n) N else 0) =
      koszulSign p q • ((if p = d then
        SuperBimodule.whiskerRight (heightInductionSuperDot D Sc i a ha n) M else 0) ≫
          SuperBimodule.whiskerLeft P f)
    split_ifs with h
    · subst p
      rw [SuperBimodule.super_interchange P f (heightInductionSuperDot_parity D Sc i a ha n) hf,
        koszulSign_smul_smul]
    · simp

/-- The dot restricted to content blocks at every height. -/
def heightContentDot (β : Multiset I) :
    SuperNatTrans k (heightContentInduction D Sc i a ha n β).toFunctor
      (heightContentInduction D Sc i a ha n β).toFunctor :=
  fullLiftTrans _ _ (heightContentSupported_induction D Sc i a ha n β)
    (heightContentSupported_induction D Sc i a ha n β) (heightSuperInductionDot D Sc i a ha n)

/-- A supernatural endomorphism followed by an identity transport. -/
def heightContentCastTrans {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m') (hγ : γ = γ')
    {F : C ⥤ ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)}
    [F.Additive] [F.Linear k] [IsSuperfunctor k F] (η : SuperNatTrans k F F) :
    SuperNatTrans k (F ⋙ (heightContentCast D Sc a ha hm hγ).toFunctor)
      (F ⋙ (heightContentCast D Sc a ha hm hγ).toFunctor) := by
  subst hm
  subst hγ
  exact η

/-- **The dot on global content induction**, `δ = {i} + β`. -/
def globalContentDot {β δ : Multiset I} (h : {i} + β = δ) :
    SuperNatTrans k (globalContentInduction D Sc i a ha h).toFunctor
      (globalContentInduction D Sc i a ha h).toFunctor :=
  heightContentCastTrans D Sc a ha (card_of_add i h) h (heightContentDot D Sc i a ha β.card β)

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

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

end Transport

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

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
end

end
