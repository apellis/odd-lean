/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVPScalarBalance
import OddMath.QuiverHecke.CyclotomicAction.ELVQPProduct

/-!
# Append balance over the signed ELV coefficient category

The old-generator balance calculation of `DeformedGlobalQP.md` §4, in the
append presentation. The moving relation is the full homogeneous ELV relation,
not a polynomial over an ordinary commutative coefficient ring.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

set_option quotPrecheck false in
local notation "O[" l "]" => (pres D Sc).obj (ob D l)

/-- The homogeneous old-generator morphism, with the full ELV relation. -/
def appendW (i : I) (s : List I) : hom D Sc cutoff (s ++ [i]) (i :: s) :=
  affineUnit D Sc cutoff _ _ (lastToFirstHom D Sc i s) ≫ relation D Sc cutoff i s

/-- Total parity, including the exterior coefficients of the relation. -/
def appendQ (i : I) (s : List I) : ZMod 2 :=
  D.parity i * wordSumParity D s + (cutoff i : ZMod 2) * D.parity i

/-- The error is linear in the full coefficient-category morphism. -/
def appendError (i : I) (s t : List I) : hom D Sc cutoff s t →ₗ[k]
    hom D Sc cutoff (s ++ [i]) (i :: t) where
  toFun g := rightContext D Sc cutoff [i] s t g ≫ appendW D Sc cutoff i t -
    appendW D Sc cutoff i s ≫ insert D Sc cutoff i s t (twist k (appendQ D cutoff i s) g)
  map_add' f g := by
    simp only [map_add, Preadditive.add_comp, Preadditive.comp_add]
    abel
  map_smul' c f := by
    simp only [map_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply, smul_sub]

@[simp] theorem appendError_apply (i : I) {s t : List I} (g : hom D Sc cutoff s t) :
    appendError D Sc cutoff i s t g =
      rightContext D Sc cutoff [i] s t g ≫ appendW D Sc cutoff i t -
        appendW D Sc cutoff i s ≫ insert D Sc cutoff i s t
          (twist k (appendQ D cutoff i s) g) := rfl

theorem appendW_mem (i : I) (s : List I) :
    appendW D Sc cutoff i s ∈ parity (R := k) _ _ (appendQ D cutoff i s) :=
  comp_mem (ELVPScalar.affineUnit_mem D Sc cutoff (lastToFirstHom_mem D Sc s))
    (relation_mem_parity D Sc cutoff i s)

theorem appendW_mem_ideal (i : I) (s : List I) :
    appendW D Sc cutoff i s ∈ ideal D Sc cutoff (s ++ [i]) (i :: s) :=
  comp_ideal D Sc cutoff _ (relation_mem D Sc cutoff i s)

theorem appendQ_append (i x : I) (s : List I) :
    appendQ D cutoff i (s ++ [x]) = appendQ D cutoff i s + D.parity i * D.parity x := by
  simp only [appendQ, wordSumParity, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil]
  ring

@[simp] theorem rightContext_affineUnit (σ v w : List I) (f : O[v] ⟶ O[w]) :
    rightContext D Sc cutoff σ v w (affineUnit D Sc cutoff v w f) =
      affineUnit D Sc cutoff _ _ (affineRightContext D Sc σ v w f) := rfl

@[simp] theorem insert_affineUnit (i : I) (v w : List I) (f : O[v] ⟶ O[w]) :
    insert D Sc cutoff i v w (affineUnit D Sc cutoff v w f) =
      affineUnit D Sc cutoff _ _ (affineInsert D Sc i v w f) := rfl

@[simp] theorem rightContext_id (σ v : List I) :
    rightContext D Sc cutoff σ v v (𝟙 _) = 𝟙 _ := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    ((𝟙 O[v]) ▷ O[σ]) = _
  rw [MonoidalSupercategory.id_whiskerRight (R := k)]
  rfl

/-- Peeling a last old letter requires no assumption on coefficients. -/
theorem appendW_append (i : I) (s : List I) (x : I) :
    appendW D Sc cutoff i (s ++ [x]) =
      affineUnit D Sc cutoff _ _ (crossLast D Sc s x i) ≫
        rightContext D Sc cutoff [x] _ _ (appendW D Sc cutoff i s) := by
  rw [appendW, appendW, lastToFirstHom_append_singleton, affineUnit_comp,
    rightContext_comp, rightContext_relation, rightContext_affineUnit, Category.assoc]
  rfl

private theorem append_induction_hom {v w : List I} {P : hom D Sc cutoff v w → Prop}
    (y : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (r s : ZMod 2)
      (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst) (f : O[v] ⟶ O[w]),
      a ∈ parity (R := k) _ _ r → f ∈ parity (R := k) _ _ s →
      P (BoxProd.tmulHom a f))
    (add : ∀ y z, P y → P z → P (y + z)) : P y :=
  BoxProd.induction_on_homogeneous (P := P) y zero tmul add

/-- Lift a twisted affine square to the signed box product. The coefficient parity
contributes a second Koszul sign; it is not legitimate to treat coefficients as even. -/
theorem lift_twisted_square {v w a b c d : List I} {p : ZMod 2}
    (L : (O[v] ⟶ O[w]) →ₗ[k] (O[a] ⟶ O[b]))
    (R : (O[v] ⟶ O[w]) →ₗ[k] (O[c] ⟶ O[d]))
    (u : O[a] ⟶ O[c]) (z : O[b] ⟶ O[d])
    (hz : z ∈ parity (R := k) _ _ p)
    (hR : ∀ {s : ZMod 2} {f : O[v] ⟶ O[w]},
      f ∈ parity (R := k) _ _ s → R f ∈ parity (R := k) _ _ s)
    (hsquare : ∀ f, u ≫ R f = L (twist k p f) ≫ z)
    (y : hom D Sc cutoff v w) :
    affineUnit D Sc cutoff a c u ≫ TensorProduct.map LinearMap.id R y =
      TensorProduct.map LinearMap.id L (twist k p y) ≫ affineUnit D Sc cutoff b d z := by
  induction y using append_induction_hom D Sc cutoff with
  | zero => simp only [map_zero, Limits.comp_zero, Limits.zero_comp]
  | add y y' hy hy' =>
    simp only [map_add]
    change (affineUnit D Sc cutoff a c u : hom D Sc cutoff a c) ≫
      ((TensorProduct.map LinearMap.id R y : hom D Sc cutoff c d) +
        TensorProduct.map LinearMap.id R y') =
      ((TensorProduct.map LinearMap.id L (twist k p y) : hom D Sc cutoff a b) +
        TensorProduct.map LinearMap.id L (twist k p y')) ≫ affineUnit D Sc cutoff b d z
    exact (Preadditive.comp_add _ _ _ _ _ _).trans
      ((congrArg₂ (· + ·) hy hy').trans (Preadditive.add_comp _ _ _ _ _ _).symm)
  | tmul r s aa f ha hf =>
    have ht := BoxProd.tmul_mem_parity (X := obj D Sc cutoff v)
      (Y := obj D Sc cutoff w) ha hf
    change BoxProd.tmulHom aa f ∈ parity (R := k) _ _ (r + s) at ht
    rw [twist_of_mem p ht, ← koszulSign_smul, map_zsmul, Preadditive.zsmul_comp]
    change BoxProd.tmulHom (X := obj D Sc cutoff a) (Y := obj D Sc cutoff c) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) u ≫
        BoxProd.tmulHom (X := obj D Sc cutoff c) (Y := obj D Sc cutoff d) aa (R f) =
      koszulSign p (r + s) •
        (BoxProd.tmulHom (X := obj D Sc cutoff a) (Y := obj D Sc cutoff b) aa (L f) ≫
          BoxProd.tmulHom (X := obj D Sc cutoff b) (Y := obj D Sc cutoff d) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) z)
    rw [BoxProd.tmulHom_comp_tmulHom (X := obj D Sc cutoff a)
      (Y := obj D Sc cutoff c) (Z := obj D Sc cutoff d)
      (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
        SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem) u aa (hR hf),
      BoxProd.tmulHom_comp_tmulHom (X := obj D Sc cutoff a)
        (Y := obj D Sc cutoff b) (Z := obj D Sc cutoff d) ha (L f) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) hz]
    simp only [koszulSign_zero_left, one_smul]
    change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff at aa
    change (aa * 1) ⊗ₜ[k] (u ≫ R f) =
      koszulSign p (r + s) • (koszulSign r p • ((1 * aa) ⊗ₜ[k] (L f ≫ z)))
    rw [mul_one, one_mul, hsquare, twist_of_mem p hf, ← koszulSign_smul,
      map_zsmul, Preadditive.zsmul_comp, TensorProduct.tmul_smul, smul_smul]
    rw [koszulSign_add_right, koszulSign_comm r p]
    rw [mul_right_comm, koszulSign_mul_self, one_mul]

/-- A trailing homogeneous affine morphism passes an arbitrary ELV morphism. -/
theorem trailing_comp_rightContext {v w σ τ : List I} {p : ZMod 2}
    {c : O[σ] ⟶ O[τ]} (hc : c ∈ parity (R := k) _ _ p)
    (y : hom D Sc cutoff v w) :
    affineUnit D Sc cutoff (v ++ σ) (v ++ τ) (O[v] ◁ c) ≫ rightContext D Sc cutoff τ v w y =
      rightContext D Sc cutoff σ v w (twist k p y) ≫
        affineUnit D Sc cutoff (w ++ σ) (w ++ τ) (O[w] ◁ c) := by
  exact lift_twisted_square D Sc cutoff
    (affineRightContext D Sc σ v w) (affineRightContext D Sc τ v w)
    (O[v] ◁ c) (O[w] ◁ c)
    (MonoidalSupercategory.whiskerLeft_mem (R := k) O[w] hc)
    (fun hf => MonoidalSupercategory.whiskerRight_mem (R := k) O[τ] hf)
    (fun f => whiskerLeft_comp_whiskerRight_twist D Sc hc f) y

/-- The error of a composite is a sum of the two factor errors. -/
theorem appendError_comp (i : I) {s t u : List I}
    (hq : appendQ D cutoff i s = appendQ D cutoff i t)
    (f : hom D Sc cutoff s t) (g : hom D Sc cutoff t u) :
    appendError D Sc cutoff i s u (f ≫ g) =
      rightContext D Sc cutoff [i] s t f ≫ appendError D Sc cutoff i t u g +
        appendError D Sc cutoff i s t f ≫
          insert D Sc cutoff i t u (twist k (appendQ D cutoff i s) g) := by
  simp only [appendError_apply, twist_comp, rightContext_comp, insert_comp,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, hq]
  abel

theorem appendError_comp_mem (i : I) {s t u : List I}
    (hq : appendQ D cutoff i s = appendQ D cutoff i t)
    {f : hom D Sc cutoff s t} {g : hom D Sc cutoff t u}
    (hf : appendError D Sc cutoff i s t f ∈ appendRelations D Sc cutoff i s (i :: t))
    (hg : appendError D Sc cutoff i t u g ∈ appendRelations D Sc cutoff i t (i :: u)) :
    appendError D Sc cutoff i s u (f ≫ g) ∈ appendRelations D Sc cutoff i s (i :: u) := by
  rw [appendError_comp D Sc cutoff i hq]
  exact Submodule.add_mem _ (comp_appendRelations D Sc cutoff i f hg)
    (appendRelations_comp D Sc cutoff i hf _)

@[simp] theorem appendError_id (i : I) (s : List I) :
    appendError D Sc cutoff i s s (𝟙 _) = 0 := by
  simp only [appendError_apply, twist_id, rightContext_id, insert_id,
    Category.id_comp, Category.comp_id, sub_self]

/-- Coefficient-only balance has zero error, before quotienting. -/
theorem appendError_scalar (i : I) (s : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    appendError D Sc cutoff i s s (ELVPScalar.scalar D Sc cutoff s a) = 0 := by
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cutoff)
    (by simp) ?_ ?_ a
  · intro p a
    rw [appendError_apply, sub_eq_zero, ELVPScalar.rightContext_scalar,
      twist_of_mem _ (ELVPScalar.scalar_mem D Sc cutoff s a.property),
      map_smul, ELVPScalar.insert_scalar, Linear.comp_smul,
      ELVPScalar.scalar_slide_homogeneous D Sc cutoff a.property,
      twist_of_mem _ (appendW_mem D Sc cutoff i s), Linear.comp_smul, smul_smul,
      mul_comm p (appendQ D cutoff i s), Supercategory.sign_mul_self, one_smul]
  · intro a b ha hb
    simp only [map_add, ha, hb, add_zero]

private theorem appendW_trailing_dot (i : I) (ν : List I) (x : I) : affineUnit D Sc cutoff (ν ++ [i] ++ [x]) (ν ++ [i] ++ [x])
    (dotE D Sc (ν ++ [i] ++ [x]) (ν.length + 1)) ≫
      rightContext D Sc cutoff [x] _ _ (appendW D Sc cutoff i ν) =
    SKM.zsign k (D.parity x * appendQ D cutoff i ν) •
      (rightContext D Sc cutoff [x] _ _ (appendW D Sc cutoff i ν) ≫
        affineUnit D Sc cutoff (i :: (ν ++ [x])) (i :: (ν ++ [x])) (O[i :: ν] ◁ dotE D Sc [x] 0)) := by
  have hd := firstDot_parity D Sc x []
  rw [← whiskerLeft_dotE D Sc (ν ++ [i]) x (by simp)]
  rw [trailing_comp_rightContext D Sc cutoff (v := ν ++ [i]) (w := i :: ν) hd,
    twist_of_mem _ (appendW_mem D Sc cutoff i ν), map_smul,
    Linear.smul_comp, sign_eq_zsign]
  rfl

private theorem insert_lastDot (i : I) (ν : List I) (x : I) : insert D Sc cutoff i _ _
    (affineUnit D Sc cutoff (ν ++ [x]) (ν ++ [x]) (dotE D Sc (ν ++ [x]) ν.length)) =
    affineUnit D Sc cutoff (i :: (ν ++ [x])) (i :: (ν ++ [x])) (O[i :: ν] ◁ dotE D Sc [x] 0) := by
  rw [insert_affineUnit]
  apply congrArg (affineUnit D Sc cutoff (i :: (ν ++ [x])) (i :: (ν ++ [x])))
  change O[[i]] ◁ dotE D Sc (ν ++ [x]) ν.length = _
  rw [whiskerLeft_letter_dotE,
    whiskerLeft_dotE D Sc (i :: ν) x (a := ν.length + 1) (by simp)]
  rfl

/-- The last old dot error is zero off the diagonal, and the right extension
of the shorter moving relation on the diagonal. -/
theorem appendError_lastDot_mem (i : I) (ν : List I) (x : I) :
    appendError D Sc cutoff i (ν ++ [x]) (ν ++ [x])
      (affineUnit D Sc cutoff (ν ++ [x]) (ν ++ [x]) (dotE D Sc (ν ++ [x]) ν.length)) ∈
        appendRelations D Sc cutoff i (ν ++ [x]) (i :: (ν ++ [x])) := by
  have hd : dotE D Sc [x] 0 ∈ parity (R := k) _ _ (D.parity x) :=
    firstDot_parity D Sc x []
  have hg : dotE D Sc (ν ++ [x]) ν.length = O[ν] ◁ dotE D Sc [x] 0 :=
    (whiskerLeft_dotE D Sc ν x rfl).symm
  have hgm : affineUnit D Sc cutoff (ν ++ [x]) (ν ++ [x]) (dotE D Sc (ν ++ [x]) ν.length) ∈
      parity (R := k) _ _ (D.parity x) := by
    apply ELVPScalar.affineUnit_mem
    rw [hg]
    exact MonoidalSupercategory.whiskerLeft_mem (R := k) O[ν] hd
  have hR := insert_lastDot D Sc cutoff i ν x
  have hL := appendW_trailing_dot D Sc cutoff i ν x
  have hright : rightContext D Sc cutoff [i] _ _
      (affineUnit D Sc cutoff (ν ++ [x]) (ν ++ [x]) (dotE D Sc (ν ++ [x]) ν.length)) =
      affineUnit D Sc cutoff (ν ++ [x] ++ [i]) (ν ++ [x] ++ [i]) (dotE D Sc (ν ++ [x] ++ [i]) ν.length) := by
    rw [rightContext_affineUnit]
    exact congrArg (affineUnit D Sc cutoff (ν ++ [x] ++ [i]) (ν ++ [x] ++ [i]))
      (dotE_whiskerRight D Sc (ν ++ [x]) [i] ν.length (by simp))
  rw [appendError_apply, appendW_append, hright, twist_of_mem _ hgm,
    map_smul, hR, sign_eq_zsign, appendQ_append, ← Category.assoc, ← affineUnit_comp]
  rcases eq_or_ne x i with rfl | hx
  · rw [dotE_comp_crossLast_self, map_add, map_smul, affineUnit_comp,
      affineUnit_id, Preadditive.add_comp, Linear.smul_comp, Category.assoc, hL,
      Category.id_comp, Linear.comp_smul, Linear.comp_smul, smul_smul,
      zsign_lastDot, Category.assoc, add_sub_cancel_left]
    simpa only [List.cons_append] using
      (rightContext_mem_appendRelations D Sc cutoff x (v := ν ++ [x]) (t := x :: ν)
        (appendW_mem_ideal D Sc cutoff x ν))
  · rw [dotE_comp_crossLast_ne D Sc ν hx, map_smul, affineUnit_comp,
      Linear.smul_comp, Category.assoc, hL, Linear.comp_smul, Linear.comp_smul,
      smul_smul, zsign_lastDot, Category.assoc, sub_self]
    exact Submodule.zero_mem _

/-- The last moving dot power passes an old ideal element with the total parity twist. -/
theorem trailing_dotPower_comp_mem_appendRelations (i : I) {n t : List I}
    {Y : hom D Sc cutoff n (i :: t)} (hY : Y ∈ ideal D Sc cutoff n (i :: t)) (e : ℕ) :
    affineUnit D Sc cutoff (n ++ [i]) (n ++ [i]) (O[n] ◁ (dotE D Sc [i] 0 ^ e)) ≫
      rightContext D Sc cutoff [i] _ _ Y ∈
        appendRelations D Sc cutoff i n (i :: (t ++ [i])) := by
  rw [trailing_comp_rightContext D Sc cutoff (v := n) (w := i :: t) (firstDot_pow_parity D Sc i [] e)]
  exact appendRelations_mem D Sc cutoff i (twist_ideal D Sc cutoff _ hY) _

/-- A final crossing passes any full coefficient-category morphism. -/
theorem crossLast_comp_rightContext {s t : List I} (x z : I)
    (y : hom D Sc cutoff s t) :
    affineUnit D Sc cutoff (s ++ [x] ++ [z]) (s ++ [z] ++ [x]) (crossLast D Sc s x z) ≫
      rightContext D Sc cutoff [x] _ _ (rightContext D Sc cutoff [z] _ _ y) =
    rightContext D Sc cutoff [z] _ _ (rightContext D Sc cutoff [x] _ _
      (twist k (D.parity x * D.parity z) y)) ≫
        affineUnit D Sc cutoff (t ++ [x] ++ [z]) (t ++ [z] ++ [x]) (crossLast D Sc t x z) := by
  let L := (affineRightContext D Sc [z] (s ++ [x]) (t ++ [x])).comp
    (affineRightContext D Sc [x] s t)
  let R := (affineRightContext D Sc [x] (s ++ [z]) (t ++ [z])).comp
    (affineRightContext D Sc [z] s t)
  have h := lift_twisted_square D Sc cutoff L R
    (crossLast D Sc s x z) (crossLast D Sc t x z) (crossLast_mem D Sc t x z)
    (fun hf => MonoidalSupercategory.whiskerRight_mem (R := k) O[[x]]
      (MonoidalSupercategory.whiskerRight_mem (R := k) O[[z]] hf))
    (fun f => crossLast_comp_whiskerRight D Sc x z f) y
  change affineUnit D Sc cutoff (s ++ [x] ++ [z]) (s ++ [z] ++ [x])
      (crossLast D Sc s x z) ≫
      TensorProduct.map LinearMap.id (affineRightContext D Sc [x] (s ++ [z]) (t ++ [z]))
        (TensorProduct.map LinearMap.id (affineRightContext D Sc [z] s t) y) =
    TensorProduct.map LinearMap.id (affineRightContext D Sc [z] (s ++ [x]) (t ++ [x]))
      (TensorProduct.map LinearMap.id (affineRightContext D Sc [x] s t)
        (twist k (D.parity x * D.parity z) y)) ≫
      affineUnit D Sc cutoff (t ++ [x] ++ [z]) (t ++ [z] ++ [x]) (crossLast D Sc t x z)
  simp only [TensorProduct.map_map, LinearMap.id_comp]
  exact h

/-- Crossing reduction: the only possible error is the affine braid correction,
followed by the full ELV moving relation. -/
theorem appendError_crossLast (i : I) (m : List I) (c x : I) :
    appendError D Sc cutoff i (m ++ [c] ++ [x]) (m ++ [x] ++ [c])
      (affineUnit D Sc cutoff (m ++ [c] ++ [x]) (m ++ [x] ++ [c]) (crossLast D Sc m c x)) =
    affineUnit D Sc cutoff (m ++ [c] ++ [x] ++ [i]) (m ++ [i] ++ [x] ++ [c])
      (((crossLast D Sc m c x ▷ O[[i]]) ≫ crossLast D Sc (m ++ [x]) c i ≫
          (crossLast D Sc m x i ▷ O[[c]]) :
          O[m ++ [c] ++ [x] ++ [i]] ⟶ O[m ++ [i] ++ [x] ++ [c]]) -
        (crossLast D Sc (m ++ [c]) x i ≫ (crossLast D Sc m c i ▷ O[[x]]) ≫
          crossLast D Sc (m ++ [i]) c x :
          O[m ++ [c] ++ [x] ++ [i]] ⟶ O[m ++ [i] ++ [x] ++ [c]])) ≫
      rightContext D Sc cutoff [c] _ _
        (rightContext D Sc cutoff [x] _ _ (appendW D Sc cutoff i m)) := by
  have hs : sign k (appendQ D cutoff i (m ++ [c] ++ [x]) * (D.parity c * D.parity x)) *
      sign k (D.parity c * D.parity x * appendQ D cutoff i m) = 1 := by
    rw [sign_eq_zsign, sign_eq_zsign, ← zsign_add_aux, appendQ_append, appendQ_append,
      parity_lastCross]
    simp [SKM.zsign]
  have hsw : rightContext D Sc cutoff [x] _ _
      (rightContext D Sc cutoff [c] _ _ (appendW D Sc cutoff i m)) ≫
      affineUnit D Sc cutoff (i :: (m ++ [c] ++ [x])) (i :: (m ++ [x] ++ [c])) (crossLast D Sc (i :: m) c x) =
      sign k (D.parity c * D.parity x * appendQ D cutoff i m) •
        (affineUnit D Sc cutoff (m ++ [i] ++ [c] ++ [x]) (m ++ [i] ++ [x] ++ [c]) (crossLast D Sc (m ++ [i]) c x) ≫
          rightContext D Sc cutoff [c] _ _
            (rightContext D Sc cutoff [x] _ _ (appendW D Sc cutoff i m))) := by
    have h := crossLast_comp_rightContext D Sc cutoff c x
      (twist k (D.parity c * D.parity x) (appendW D Sc cutoff i m))
    rw [twist_twist, twist_of_mem _ (appendW_mem D Sc cutoff i m),
      map_smul, map_smul, Linear.comp_smul] at h
    exact h.symm
  have hc : insert D Sc cutoff i _ _
      (affineUnit D Sc cutoff (m ++ [c] ++ [x]) (m ++ [x] ++ [c]) (crossLast D Sc m c x)) =
      affineUnit D Sc cutoff (i :: (m ++ [c] ++ [x])) (i :: (m ++ [x] ++ [c])) (crossLast D Sc (i :: m) c x) := by
    rw [insert_affineUnit]
    exact congrArg (affineUnit D Sc cutoff (i :: (m ++ [c] ++ [x])) (i :: (m ++ [x] ++ [c]))) (whiskerLeft_crossLast D Sc i m c x)
  rw [appendError_apply,
    twist_of_mem _ (ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc m c x)),
    map_smul, hc, appendW_append D Sc cutoff i (m ++ [x]) c,
    appendW_append D Sc cutoff i (m ++ [c]) x,
    appendW_append D Sc cutoff i m x, appendW_append D Sc cutoff i m c]
  simp only [rightContext_comp, rightContext_affineUnit, affineRightContext,
    Category.assoc, Linear.comp_smul]
  erw [hsw]
  rw [Linear.comp_smul, Linear.comp_smul, smul_smul, hs, one_smul,
    map_sub, Preadditive.sub_comp]
  simp only [affineUnit_comp, Category.assoc]
  rfl

/-- Every monomial in the exceptional braid correction is an append-old relation. -/
theorem braid_comp_mem_appendRelations (i : I) (m : List I) {x : I}
    (hx : i ≠ x) {LA LB : List PG}
    (eA : LA = [.cross m.length, .cross (m.length + 1), .cross m.length])
    (eB : LB = [.cross (m.length + 1), .cross m.length, .cross (m.length + 1)])
    (hA : SChain (m ++ [i] ++ [x] ++ [i]) (pl (m ++ [i] ++ [x] ++ [i]) LA)
      (m ++ [i] ++ [x] ++ [i]))
    (hB : SChain (m ++ [i] ++ [x] ++ [i]) (pl (m ++ [i] ++ [x] ++ [i]) LB)
      (m ++ [i] ++ [x] ++ [i])) :
    affineUnit D Sc cutoff (m ++ [i] ++ [x] ++ [i]) (m ++ [i] ++ [x] ++ [i]) (cl D Sc _ _ _ hA - cl D Sc _ _ _ hB) ≫
      rightContext D Sc cutoff [i] _ _
        (rightContext D Sc cutoff [x] _ _ (appendW D Sc cutoff i m)) ∈
      appendRelations D Sc cutoff i (m ++ [i] ++ [x]) (i :: (m ++ [x] ++ [i])) := by
  subst eA eB
  rw [IntertwinerMeet.braid_iji_gen D Sc m [] hx (by simp) rfl hA hB]
  have hu : ∀ (q : ℕ), q < (m ++ [i] ++ [x]).length → ∀ e : ℕ,
      dotE D Sc (m ++ [i] ++ [x] ++ [i]) q ^ e =
        (dotE D Sc (m ++ [i] ++ [x]) q ^ e) ▷ O[[i]] := by
    intro q hq e
    rw [← whiskerListAlgHom_apply, map_pow, whiskerListAlgHom_apply,
      dotE_whiskerRight D Sc _ [i] q hq]
  have hw : ∀ e : ℕ, dotE D Sc (m ++ [i] ++ [x] ++ [i]) (m.length + 2) ^ e =
      O[m ++ [i] ++ [x]] ◁ (dotE D Sc [i] 0 ^ e) := by
    intro e
    rw [dotE_pow, dotE_pow, cl_whiskerLeft]
    exact cl_congr_gs D Sc (by simp [PG.shift]) _ _
  let L : End O[m ++ [i] ++ [x] ++ [i]] →ₗ[k]
      hom D Sc cutoff (m ++ [i] ++ [x] ++ [i]) (i :: (m ++ [x] ++ [i])) :=
    (Linear.rightComp k _ (rightContext D Sc cutoff [i] _ _
      (rightContext D Sc cutoff [x] _ _ (appendW D Sc cutoff i m)))).comp
        (affineUnit D Sc cutoff (m ++ [i] ++ [x] ++ [i]) (m ++ [i] ++ [x] ++ [i]))
  have hmon : ∀ e₁ e₂ e₃ : ℕ,
      (dotE D Sc (m ++ [i] ++ [x] ++ [i]) m.length ^ e₁ *
        dotE D Sc (m ++ [i] ++ [x] ++ [i]) (m.length + 1) ^ e₂ *
        dotE D Sc (m ++ [i] ++ [x] ++ [i]) (m.length + 2) ^ e₃) ∈
      (appendRelations D Sc cutoff i (m ++ [i] ++ [x])
        (i :: (m ++ [x] ++ [i]))).comap L := by
    intro e₁ e₂ e₃
    rw [Submodule.mem_comap]
    change affineUnit D Sc cutoff (m ++ [i] ++ [x] ++ [i])
      (m ++ [i] ++ [x] ++ [i]) _ ≫ _ ∈
        appendRelations D Sc cutoff i (m ++ [i] ++ [x]) (i :: (m ++ [x] ++ [i]))
    rw [End.mul_def, End.mul_def,
      affineUnit_comp (v := m ++ [i] ++ [x] ++ [i])
        (w := m ++ [i] ++ [x] ++ [i]) (z := m ++ [i] ++ [x] ++ [i]),
      affineUnit_comp (v := m ++ [i] ++ [x] ++ [i])
        (w := m ++ [i] ++ [x] ++ [i]) (z := m ++ [i] ++ [x] ++ [i]),
      hw, hu _ (by simp) e₁, hu _ (by simp) e₂]
    have hY := comp_ideal D Sc cutoff
      (affineUnit D Sc cutoff (m ++ [i] ++ [x]) (m ++ [i] ++ [x]) (dotE D Sc (m ++ [i] ++ [x]) (m.length + 1) ^ e₂))
      (comp_ideal D Sc cutoff
        (affineUnit D Sc cutoff (m ++ [i] ++ [x]) (m ++ [i] ++ [x]) (dotE D Sc (m ++ [i] ++ [x]) m.length ^ e₁))
        (ideal_rightContext D Sc cutoff [x] (appendW_mem_ideal D Sc cutoff i m)))
    have h := trailing_dotPower_comp_mem_appendRelations D Sc cutoff i
      (t := m ++ [x]) hY e₃
    rw [rightContext_comp, rightContext_comp, rightContext_affineUnit,
      rightContext_affineUnit] at h
    simpa only [List.cons_append, Category.assoc, affineRightContext, LinearMap.coe_mk, AddHom.coe_mk] using h
  change L _ ∈ _
  rw [← Submodule.mem_comap]
  unfold IntertwinerMeet.braidCorr
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ ?_)
    (Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
      Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hmon _ _ _))
  have h := hmon (D.dn i x - 1 - r) 0 r
  rwa [pow_zero, mul_one] at h

private theorem affineUnit_sub_comp_mem_of_eq {s t v : List I} {f g : O[s] ⟶ O[t]}
    (h : f = g) (z : hom D Sc cutoff t v) (K : Submodule k (hom D Sc cutoff s v)) :
    affineUnit D Sc cutoff s t (f - g) ≫ z ∈ K := by
  rw [h, sub_self, map_zero, Limits.zero_comp]
  exact Submodule.zero_mem _

/-- The crossing of the last two old strands is balanced, including the exceptional
`(i,x,i)` window; its correction is killed by the old relation, not the moving one. -/
theorem appendError_crossLast_mem (i : I) (m : List I) (c x : I) :
    appendError D Sc cutoff i (m ++ [c] ++ [x]) (m ++ [x] ++ [c])
      (affineUnit D Sc cutoff (m ++ [c] ++ [x]) (m ++ [x] ++ [c]) (crossLast D Sc m c x)) ∈
        appendRelations D Sc cutoff i (m ++ [c] ++ [x]) (i :: (m ++ [x] ++ [c])) := by
  rw [appendError_crossLast, crossLast_whiskerRight_cl, crossLast_whiskerRight_cl,
    crossLast_whiskerRight_cl, crossLast, crossLast, crossLast, cl_comp_three, cl_comp_three]
  by_cases hb : c = i ∧ c ≠ x
  · obtain ⟨rfl, hx⟩ := hb
    refine braid_comp_mem_appendRelations D Sc cutoff _ m hx ?_ ?_ _ _ <;> simp
  · refine affineUnit_sub_comp_mem_of_eq D Sc cutoff ?_ _ _
    refine (braid_ne_gen D Sc m [] c x i hb ?_ ?_ ?_ ?_ _ _).symm <;> simp

/-- Right extension preserves the total parity twist. -/
theorem rightContext_twist (σ : List I) (p : ZMod 2) {s t : List I}
    (g : hom D Sc cutoff s t) :
    rightContext D Sc cutoff σ s t (twist k p g) =
      twist k p (rightContext D Sc cutoff σ s t g) := by
  induction g using append_induction_hom D Sc cutoff with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul r q a f ha hf =>
    have ht := BoxProd.tmul_mem_parity (X := obj D Sc cutoff s)
      (Y := obj D Sc cutoff t) ha hf
    have ht' := BoxProd.tmul_mem_parity (X := obj D Sc cutoff (s ++ σ))
      (Y := obj D Sc cutoff (t ++ σ)) ha
      (MonoidalSupercategory.whiskerRight_mem (R := k) O[σ] hf)
    change BoxProd.tmulHom a f ∈ parity (R := k) _ _ (r + q) at ht
    rw [twist_of_mem p ht, map_smul]
    exact (twist_of_mem p ht').symm

theorem affineUnit_twist (p : ZMod 2) {s t : List I} (f : O[s] ⟶ O[t]) :
    affineUnit D Sc cutoff s t (twist k p f) =
      twist k p (affineUnit D Sc cutoff s t f) := by
  induction f using Supercategory.induction_on (R := k) (C := (pres D Sc).Presented) with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | hom q f hf =>
    rw [twist_of_mem p hf, map_smul,
      twist_of_mem p (ELVPScalar.affineUnit_mem D Sc cutoff hf)]

/-- Passing a spectator through a relation keeps it in the append-old span. -/
theorem crossLast_comp_mem_appendRelations (i x : I) {s t : List I}
    {K : hom D Sc cutoff (s ++ [i]) (i :: t)}
    (hK : K ∈ appendRelations D Sc cutoff i s (i :: t)) :
    affineUnit D Sc cutoff (s ++ [x] ++ [i]) (s ++ [i] ++ [x]) (crossLast D Sc s x i) ≫
      rightContext D Sc cutoff [x] _ _ K ∈
        appendRelations D Sc cutoff i (s ++ [x]) (i :: (t ++ [x])) := by
  induction hK using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, y, hy, h, rfl⟩ := hf
    rw [rightContext_comp, ← Category.assoc, crossLast_comp_rightContext, Category.assoc]
    exact appendRelations_mem D Sc cutoff i
      (ideal_rightContext D Sc cutoff [x] (twist_ideal D Sc cutoff _ hy)) _
  | zero =>
    rw [map_zero, Limits.comp_zero]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    rw [map_add, Preadditive.comp_add]
    exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    rw [map_smul, Linear.comp_smul]
    exact Submodule.smul_mem _ c hf

/-- Error recursion when an old morphism has a final spectator strand. -/
theorem appendError_rightContext (i x : I) {s t : List I} (f : hom D Sc cutoff s t) :
    appendError D Sc cutoff i (s ++ [x]) (t ++ [x])
      (rightContext D Sc cutoff [x] s t f) =
    affineUnit D Sc cutoff (s ++ [x] ++ [i]) (s ++ [i] ++ [x]) (crossLast D Sc s x i) ≫
      rightContext D Sc cutoff [x] _ _
        (appendError D Sc cutoff i s t (twist k (D.parity i * D.parity x) f)) := by
  rw [appendError_apply, appendError_apply, appendW_append, appendW_append,
    map_sub, Preadditive.comp_sub]
  congr 1
  · have h := crossLast_comp_rightContext D Sc cutoff x i
      (twist k (D.parity i * D.parity x) f)
    rw [mul_comm (D.parity x), twist_twist] at h
    rw [rightContext_comp, reassoc_of% h]
  · rw [rightContext_comp, Category.assoc, appendQ_append, twist_add,
      ← rightContext_twist, ← rightContext_twist, rightContext_insert]

/-- Balance passes from shorter words to an old morphism with a final spectator. -/
theorem appendError_rightContext_mem (i x : I) {s t : List I}
    {f : hom D Sc cutoff s t}
    (hf : ∀ q, appendError D Sc cutoff i s t (twist k q f) ∈
      appendRelations D Sc cutoff i s (i :: t)) :
    appendError D Sc cutoff i (s ++ [x]) (t ++ [x])
      (rightContext D Sc cutoff [x] s t f) ∈
      appendRelations D Sc cutoff i (s ++ [x]) (i :: (t ++ [x])) := by
  rw [appendError_rightContext]
  exact crossLast_comp_mem_appendRelations D Sc cutoff i x (hf _)

theorem appendQ_act (i : I) (g : PG) (t : List I) :
    appendQ D cutoff i (g.act t) = appendQ D cutoff i t := by
  simp only [appendQ]
  rw [show g.act t = tgt t [g] from rfl, wordSumParity_tgt]

/-- A generator supported away from the final letter reduces to the shorter word. -/
private theorem appendError_gen_spectator_mem (i : I) {n : ℕ}
    (ih : ∀ s t : List I, s.length < n → ∀ g : hom D Sc cutoff s t,
      appendError D Sc cutoff i s t g ∈ appendRelations D Sc cutoff i s (i :: t))
    (g : PG) (ν : List I) (x : I) {t : List I}
    (hs : ν.length + 1 = n) (hin : g.pos + g.width ≤ ν.length)
    (h : SChain (ν ++ [x]) (pl (ν ++ [x]) [g]) t) :
    appendError D Sc cutoff i (ν ++ [x]) t
      (affineUnit D Sc cutoff (ν ++ [x]) t (cl D Sc (ν ++ [x]) t [g] h)) ∈
      appendRelations D Sc cutoff i (ν ++ [x]) (i :: t) := by
  have hF : Fits ν.length [g] := by
    intro g' hg'
    simp only [List.mem_singleton] at hg'
    subst g'
    exact hin
  obtain rfl : tgt ν [g] ++ [x] = t :=
    sChain_target (sChain_append_one x (sChain_pl ν [g]) hF) h
  have he : cl D Sc (ν ++ [x]) (tgt ν [g] ++ [x]) [g] h =
      cl D Sc ν (tgt ν [g]) [g] (sChain_pl ν [g]) ▷ O[[x]] :=
    (cl_whiskerRight D Sc [g] (sChain_pl ν [g]) [x] hF).symm
  have hb := appendError_rightContext_mem D Sc cutoff i x
    (s := ν) (t := tgt ν [g])
    (f := affineUnit D Sc cutoff ν (tgt ν [g])
      (cl D Sc ν (tgt ν [g]) [g] (sChain_pl ν [g])))
    (fun q => ih ν (tgt ν [g]) (by omega) _)
  rw [rightContext_affineUnit] at hb
  rw [he]
  exact hb

/-- A positioned dot or crossing, using balance only for strictly shorter words. -/
theorem appendError_gen_mem (i : I) {n : ℕ}
    (ih : ∀ s t : List I, s.length < n → ∀ g : hom D Sc cutoff s t,
      appendError D Sc cutoff i s t g ∈ appendRelations D Sc cutoff i s (i :: t))
    (g : PG) {s t : List I} (hs : s.length = n) (h : SChain s (pl s [g]) t) :
    appendError D Sc cutoff i s t (affineUnit D Sc cutoff s t (cl D Sc s t [g] h)) ∈
      appendRelations D Sc cutoff i s (i :: t) := by
  by_cases hfit : g.pos + g.width ≤ s.length
  swap
  · obtain ⟨hld, -⟩ := ld_act_of_lt (g := g) (t := s) (by omega)
    have hpl : pl s [g] = pl s [] := by simp [hld]
    have h' : SChain s (pl s []) t := hpl ▸ h
    have ht : s = t := h'
    subst ht
    rw [cl_congr D Sc h h' hpl, cl_nil, affineUnit_id, appendError_id]
    exact Submodule.zero_mem _
  obtain rfl | ⟨ν, x, rfl⟩ : s = [] ∨ ∃ ν x, s = ν ++ [x] := by
    rcases List.eq_nil_or_concat s with h | ⟨ν, x, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨ν, x, by simpa using h⟩
  · cases g <;> simp [PG.pos, PG.width] at hfit
  by_cases hin : g.pos + g.width ≤ ν.length
  · exact appendError_gen_spectator_mem D Sc cutoff i ih g ν x
      (by simpa only [List.length_append, List.length_singleton] using hs) hin h
  · cases g with
    | dot p =>
      simp only [PG.pos, PG.width, List.length_append, List.length_singleton] at hfit hin
      obtain rfl : p = ν.length := by omega
      obtain rfl : ν ++ [x] = t := sChain_target (sChain_dotAny _ ν.length) h
      rw [← dotE_eq_cl D Sc h]
      exact appendError_lastDot_mem D Sc cutoff i ν x
    | cross b =>
      simp only [PG.pos, PG.width, List.length_append, List.length_singleton] at hfit hin
      obtain rfl | ⟨m, c, rfl⟩ : ν = [] ∨ ∃ m c, ν = m ++ [c] := by
        rcases List.eq_nil_or_concat ν with h | ⟨m, c, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨m, c, by simpa using h⟩
      · simp at hfit hin
      simp only [List.length_append, List.length_singleton] at hfit hin
      obtain rfl : b = m.length := by omega
      obtain rfl : m ++ [x] ++ [c] = t :=
        sChain_target (by simpa using sChain_crossAt m [] c x) h
      exact appendError_crossLast_mem D Sc cutoff i m c x

/-- Balance along a positioned word follows by the composition error identity. -/
theorem appendError_cl_mem (i : I) {n : ℕ}
    (ih : ∀ s t : List I, s.length < n → ∀ g : hom D Sc cutoff s t,
      appendError D Sc cutoff i s t g ∈ appendRelations D Sc cutoff i s (i :: t))
    (gs : List PG) {s t : List I} (hs : s.length = n) (h : SChain s (pl s gs) t) :
    appendError D Sc cutoff i s t (affineUnit D Sc cutoff s t (cl D Sc s t gs h)) ∈
      appendRelations D Sc cutoff i s (i :: t) := by
  induction gs generalizing s with
  | nil =>
    obtain rfl : s = t := h
    rw [cl_nil, affineUnit_id, appendError_id]
    exact Submodule.zero_mem _
  | cons g gs ihg =>
    have e := cl_append D Sc [g] gs h
    rw [show cl D Sc s t (g :: gs) h = _ from e, affineUnit_comp]
    refine appendError_comp_mem D Sc cutoff i (appendQ_act D cutoff i g s).symm
      (appendError_gen_mem D Sc cutoff i ih g hs _) (ihg ?_ _)
    rw [length_act, hs]

/-- A pure tensor factors through the affine unit and a target coefficient, with no
sign: the affine unit's coefficient is even. -/
theorem affineUnit_comp_scalar {s t : List I} (f : O[s] ⟶ O[t])
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    affineUnit D Sc cutoff s t f ≫ ELVPScalar.scalar D Sc cutoff t a = a ⊗ₜ[k] f := by
  change BoxProd.tmulHom (X := obj D Sc cutoff s) (Y := obj D Sc cutoff t)
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) f ≫
    BoxProd.tmulHom (X := obj D Sc cutoff t) (Y := obj D Sc cutoff t) a (𝟙 _) = _
  rw [BoxProd.tmulHom_comp_tmulHom (X := obj D Sc cutoff s)
    (Y := obj D Sc cutoff t) (Z := obj D Sc cutoff t)
    (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
      SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem)
    f a (id_mem (R := k) _)]
  simp only [koszulSign_zero_left, one_smul, Category.comp_id]
  change (a * 1) ⊗ₜ[k] f = _
  rw [mul_one]

/-- Balance of the append moving-strand map for every full ELV morphism.
The induction includes all exterior coefficients and all old dots and crossings. -/
theorem appendError_mem_appendRelations (i : I) {s t : List I}
    (g : hom D Sc cutoff s t) :
    appendError D Sc cutoff i s t g ∈ appendRelations D Sc cutoff i s (i :: t) := by
  suffices H : ∀ n (s t : List I), s.length = n → ∀ g : hom D Sc cutoff s t,
      appendError D Sc cutoff i s t g ∈ appendRelations D Sc cutoff i s (i :: t) from
    H _ s t rfl g
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hs g
    have ih' : ∀ s t : List I, s.length < n → ∀ g : hom D Sc cutoff s t,
        appendError D Sc cutoff i s t g ∈ appendRelations D Sc cutoff i s (i :: t) :=
      fun s t hlt g => ih _ hlt s t rfl g
    induction g using TensorProduct.inductionOn with
    | add f g hf hg =>
      rw [map_add]
      exact Submodule.add_mem _ hf hg
    | tmul a f =>
      let L := (appendError D Sc cutoff i s t).comp
        (TensorProduct.mk k (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ a)
      have hle : Submodule.span k {f : O[s] ⟶ O[t] |
          ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < s.length) ∧
            ∃ w : Equiv.Perm (Fin s.length),
              ∃ h, cl D Sc s t (l.map PG.dot ++ cw (Categorification.TypeA.canWord s.length w)) h = f} ≤
          (appendRelations D Sc cutoff i s (i :: t)).comap L := by
        rw [Submodule.span_le]
        rintro _ ⟨l, -, -, w, h, rfl⟩
        change appendError D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc s t _ h) ∈
          appendRelations D Sc cutoff i s (i :: t)
        rw [← affineUnit_comp_scalar]
        have ht := sChain_target (sChain_pl s
          (l.map PG.dot ++ cw (Categorification.TypeA.canWord s.length w))) h
        have hq : appendQ D cutoff i s = appendQ D cutoff i t := by
          unfold appendQ
          rw [← ht, wordSumParity_tgt]
        apply appendError_comp_mem D Sc cutoff i hq
        · exact appendError_cl_mem D Sc cutoff i ih' _ hs h
        · rw [appendError_scalar]
          exact Submodule.zero_mem _
      rw [span_normalForms D Sc s t] at hle
      exact hle Submodule.mem_top

end OddMath.QuiverHecke.ELVOld
