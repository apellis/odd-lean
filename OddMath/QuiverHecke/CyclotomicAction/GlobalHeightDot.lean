/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction
import OddMath.QuiverHecke.CyclotomicAction.SuperDot

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

/-- On a homogeneous corner element the sign is explicit. -/
theorem heightInductionSuperDot_apply {p : ZMod 2} (x : (P).toSVec)
    (hx : x ∈ (P).toSVec.part p) :
    ((heightInductionSuperDot D Sc i a ha n).1 x).val =
      koszulSign p d • (x.val * c) := by
  change ((P).toSVec.sgn d x).val * c = _
  rw [SVec.sgn_apply_of_mem d hx]
  change (sign k (p * d) • x.val) * c = _
  rw [smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul]

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

/-- Only the component of the induction colour's parity is nonzero. -/
theorem heightSuperInductionDot_homogeneous :
    (heightSuperInductionDot D Sc i a ha n).IsHomogeneous d := by
  intro q h
  funext M
  simp [heightSuperInductionDot, h]

/-- The dot restricted to content blocks at every height. -/
def heightContentDot (β : Multiset I) :
    SuperNatTrans k (heightContentInduction D Sc i a ha n β).toFunctor
      (heightContentInduction D Sc i a ha n β).toFunctor :=
  fullLiftTrans _ _ (heightContentSupported_induction D Sc i a ha n β)
    (heightContentSupported_induction D Sc i a ha n β) (heightSuperInductionDot D Sc i a ha n)

theorem heightContentDot_homogeneous (β : Multiset I) :
    (heightContentDot D Sc i a ha n β).IsHomogeneous d :=
  fullLiftTrans_homogeneous _ _ _ _ _ (heightSuperInductionDot_homogeneous D Sc i a ha n)

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

theorem heightContentCastTrans_homogeneous {C : Type*} [Category C] [Preadditive C]
    [Linear k C] [Supercategory k C] {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m') (hγ : γ = γ')
    {F : C ⥤ ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)}
    [F.Additive] [F.Linear k] [IsSuperfunctor k F] (η : SuperNatTrans k F F) {p : ZMod 2}
    (hη : η.IsHomogeneous p) :
    (heightContentCastTrans D Sc a ha hm hγ η).IsHomogeneous p := by
  subst hm
  subst hγ
  exact hη

/-- **The dot on global content induction**, `δ = {i} + β`. -/
def globalContentDot {β δ : Multiset I} (h : {i} + β = δ) :
    SuperNatTrans k (globalContentInduction D Sc i a ha h).toFunctor
      (globalContentInduction D Sc i a ha h).toFunctor :=
  heightContentCastTrans D Sc a ha (card_of_add i h) h (heightContentDot D Sc i a ha β.card β)

theorem globalContentDot_homogeneous {β δ : Multiset I} (h : {i} + β = δ) :
    (globalContentDot D Sc i a ha h).IsHomogeneous d :=
  heightContentCastTrans_homogeneous D Sc a ha _ _ _
    (heightContentDot_homogeneous D Sc i a ha β.card β)

end OddMath.QuiverHecke.CyclotomicAction
