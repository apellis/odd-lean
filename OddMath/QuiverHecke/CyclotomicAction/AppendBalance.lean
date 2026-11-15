import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChains
import OddMath.QuiverHecke.AppendBasis
import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import OddMath.QuiverHecke.MixedRelations

/-!
# Append balance

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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

@[simp] theorem appendRightContext_id (σ v : List I) :
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
  simp only [appendError_apply, twist_id, appendRightContext_id, insert_id,
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
end

end

section

/-!
# The append Mackey map `P` on induced modules

`docs/Nondegeneracy/AppendMackeySource.md` §4. Let `ψ = appendAlgebra i (n+1)` and
`φ_ε = prependAlgebra i (n+1) ∘ tw_ε` (the prepend inclusion after the entrywise parity twist).
The matrix

  `W = Σ_s single (i :: s) (s ++ [i]) W_s`,  `W_s = T_s ≫ f_i(x₁)`,

satisfies, entry by entry, `W ψ(a) - φ_ε(a) W = single (i :: s) (t ++ [i]) E(g)` for
`a = single s t g`, where `E` is the balance error of `AppendBalance.lean` when the parity
`q_t` of `W_t` is `ε`. Since `E(g)` lies in the killed part (`appendError_mem_appendKill`),
`P : z ⊗ b ↦ z W ⊗ b` descends from `Ind_(φ_ε) N` to `Ind_ψ N` for every left
`Hn (n+1)`-module `N` on which the cyclotomic ideal acts by zero and the diagonal idempotent of
every word `t` with `q_t ≠ ε` acts by zero (for instance a content corner of parity `ε`).

This is the source map of the append-side Mackey boundary (`DeformedMackeyBoundary.md` §1;
Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Lemma 8.1, mirror form).

## Main results

* `InductionAlong.Ind.descend`: the map `z ⊗ n ↦ z x ⊗ n` from a balance hypothesis;
* `appendMoveMatrix_mul_append`, `prependTwist_mul_appendMoveMatrix`: the entries of `W ψ(a)`
  and `φ_ε(a) W`;
* `single_mem_cyclotomicIdeal`: the old cyclotomic ideal of morphisms lies in the cyclotomic
  ideal of the matrix algebra;
* `appendMackeyMap`: the descended map `P : Ind_(φ_ε) N → Ind_ψ N`.
-/

noncomputable section

namespace Categorification.InductionAlong.Ind

universe x y
variable {A H : Type x} [Ring A] [Ring H] {N : Type y} [AddCommGroup N] [Module A N]
  {φ ψ : A →ₙ+* H}

theorem mul_mem_of_mul_right {w : H} (hw : w * ψ 1 = w) (z : H) : z * w ∈ lIdeal (ψ 1) := by
  rw [mem_lIdeal, mul_assoc, hw]

/-- Right multiplication by `w` under a balance hypothesis: `z ⊗ n ↦ z w ⊗ n`. -/
def descend {w : H} (hw : w * ψ 1 = w)
    (hb : ∀ (z : Corner φ) (a : A) (m : N),
      (tmul ⟨z.1 * φ a * w, mul_mem_of_mul_right hw _⟩ m : Ind N ψ) =
        tmul ⟨z.1 * w, mul_mem_of_mul_right hw _⟩ (a • m)) :
    Ind N φ →ₗ[H] Ind N ψ :=
  lift (fun z m => tmul ⟨z.1 * w, mul_mem_of_mul_right hw _⟩ m)
    (fun z z' m => by rw [← add_tmul]; congr 1; exact Subtype.ext (add_mul _ _ _))
    (fun z m m' => tmul_add _ m m')
    (fun z a m => hb z a m)
    (fun b z m => by rw [smul_tmul]; congr 1; exact Subtype.ext (mul_assoc b z.1 w))

@[simp] theorem descend_tmul {w : H} (hw : w * ψ 1 = w) (hb) (z : Corner φ) (m : N) :
    descend hw hb (tmul z m) = tmul ⟨z.1 * w, mul_mem_of_mul_right hw _⟩ m := rfl

/-- A tensor whose corner factor ends in `ψ(c)`, with `c` acting by zero, vanishes. -/
theorem tmul_mul_eq_zero {X : H} (hX : X * ψ 1 = X) {c : A} (hc : ∀ m : N, c • m = 0)
    (z : H) (hm : z * (X * ψ c) ∈ lIdeal (ψ 1)) (m : N) :
    (tmul ⟨z * (X * ψ c), hm⟩ m : Ind N ψ) = 0 := by
  have e : (⟨z * (X * ψ c), hm⟩ : InductionAlong.Corner ψ) =
      MulOpposite.op c • ⟨z * X, mul_mem_of_mul_right hX z⟩ :=
    Subtype.ext (by rw [op_smul_val, mul_assoc])
  rw [e, op_smul_tmul, hc, tmul_zero]

end Categorification.InductionAlong.Ind

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory Categorification Categorification.InductionAlong
open scoped Classical

universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

section Matrix
variable (a : I → _root_.Polynomial k) (i : I) (n : ℕ)

local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

/-- `φ_ε = prependAlgebra ∘ tw_ε`: the prepend inclusion after the entrywise parity twist. -/
def prependTwist (ε : ZMod 2) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1) :=
  (((prependAlgebra D Sc i (n + 1)).comp (homMatrixTwistAlgebra D Sc (n + 1) ε) :
    Hn D Sc (n + 1) →ₙₐ[k] Hn D Sc (n + 1 + 1)) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

theorem prependTwist_single (ε : ZMod 2) (s t : Word I (n + 1))
    (g : wordObj D Sc t ⟶ wordObj D Sc s) :
    prependTwist D Sc i n ε (FiniteHomMatrix.single s t g) =
      FiniteHomMatrix.single (prependWord i s) (prependWord i t)
        (prependHom D Sc i t s (Supercategory.twist k ε g)) := by
  change prependLinear D Sc i (n + 1)
    (homMatrixTwist D Sc (n + 1) ε (FiniteHomMatrix.single s t g)) = _
  rw [homMatrixTwist_single, prependLinear_single]

theorem appendAlgebra_single (s t : Word I (n + 1)) (g : wordObj D Sc t ⟶ wordObj D Sc s) :
    ψ (FiniteHomMatrix.single s t g) =
      FiniteHomMatrix.single (appendWord i s) (appendWord i t) (appendHom D Sc i t s g) := by
  exact appendLinear_single D Sc i t s g

/-- The matrix `W = Σ_s single (i :: s) (s ++ [i]) W_s`. -/
def appendMoveMatrix : Hn D Sc (n + 1 + 1) :=
  ∑ s : Word I (n + 1), FiniteHomMatrix.single (prependWord i s) (appendWord i s)
    (appendW D Sc a i s.1 : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (prependWord i s))

omit [Fintype I] in
theorem appendHom_id (t : Word I (n + 1)) :
    appendHom D Sc i t t (𝟙 (wordObj D Sc t)) = 𝟙 _ :=
  MonoidalSupercategory.id_whiskerRight (R := k) (wordObj D Sc t) ((pres D Sc).obj (ob D [i]))

theorem single_mul_appendOne {r : Word I (n + 1 + 1)} (c : Word I (n + 1))
    (f : wordObj D Sc (appendWord i c) ⟶ wordObj D Sc r) :
    FiniteHomMatrix.single r (appendWord i c) f * ψ 1 =
      FiniteHomMatrix.single r (appendWord i c) f := by
  have h1 : (1 : Hn D Sc (n + 1)) =
      ∑ t : Word I (n + 1), FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) := rfl
  rw [h1, map_sum, Finset.mul_sum, Finset.sum_eq_single c]
  · rw [appendAlgebra_single, FiniteHomMatrix.single_mul_single, appendHom_id, Category.id_comp]
  · intro t _ ht
    rw [appendAlgebra_single, FiniteHomMatrix.single_mul_single_of_ne]
    exact fun e => ht (appendWord_injective i _ e).symm
  · intro h; exact (h (Finset.mem_univ _)).elim

theorem appendMoveMatrix_mul_appendOne :
    appendMoveMatrix D Sc a i n * ψ 1 = appendMoveMatrix D Sc a i n := by
  rw [appendMoveMatrix, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => single_mul_appendOne D Sc i n s _

/-- The entries of `W ψ(a)`. -/
theorem appendMoveMatrix_mul_append (s t : Word I (n + 1))
    (g : wordObj D Sc t ⟶ wordObj D Sc s) :
    appendMoveMatrix D Sc a i n * ψ (FiniteHomMatrix.single s t g) =
      FiniteHomMatrix.single (prependWord i s) (appendWord i t)
        (appendHom D Sc i t s g ≫ appendW D Sc a i s.1) := by
  rw [appendMoveMatrix, appendAlgebra_single, Finset.sum_mul, Finset.sum_eq_single s]
  · rw [FiniteHomMatrix.single_mul_single]
  · intro u _ hu
    rw [FiniteHomMatrix.single_mul_single_of_ne]
    exact fun e => hu (appendWord_injective i _ e)
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- The entries of `φ_ε(a) W`. -/
theorem prependTwist_mul_appendMoveMatrix (ε : ZMod 2) (s t : Word I (n + 1))
    (g : wordObj D Sc t ⟶ wordObj D Sc s) :
    prependTwist D Sc i n ε (FiniteHomMatrix.single s t g) * appendMoveMatrix D Sc a i n =
      FiniteHomMatrix.single (prependWord i s) (appendWord i t)
        (appendW D Sc a i t.1 ≫ prependHom D Sc i t s (Supercategory.twist k ε g)) := by
  rw [appendMoveMatrix, prependTwist_single, Finset.mul_sum, Finset.sum_eq_single t]
  · rw [FiniteHomMatrix.single_mul_single]
  · intro u _ hu
    rw [FiniteHomMatrix.single_mul_single_of_ne]
    exact fun e => hu (prependWord_injective i _ e).symm
  · intro h; exact (h (Finset.mem_univ _)).elim

omit [Fintype I] in
theorem matrix_single_sub {r c : Word I (n + 1 + 1)} (f g : wordObj D Sc c ⟶ wordObj D Sc r) :
    (FiniteHomMatrix.single r c (f - g) : Hn D Sc (n + 1 + 1)) =
      FiniteHomMatrix.single r c f - FiniteHomMatrix.single r c g :=
  by convert DFinsupp.single_sub (β := fun p : Word I (n + 1 + 1) × Word I (n + 1 + 1) =>
    (wordObj D Sc p.2 ⟶ wordObj D Sc p.1)) (r, c) f g

omit [Fintype I] in
theorem length_eq_of_hom_ne_zero {s : Word I (n + 1)} {w : List I}
    {p : wordObj D Sc s ⟶ (pres D Sc).obj (ob D w)} (hp : p ≠ 0) : w.length = n + 1 := by
  by_contra hl
  refine hp (hom_eq_zero_of_content_ne D Sc (fun h => hl ?_) p)
  have := congrArg Multiset.card h
  simpa [s.2] using this.symm

/-- The old cyclotomic ideal of morphisms lies in the cyclotomic ideal of `Hn (n+1)`. -/
theorem single_mem_cyclotomicIdeal (u t : Word I (n + 1))
    {y : wordObj D Sc t ⟶ wordObj D Sc u} (hy : y ∈ cycHom D Sc a t.1 u.1) :
    FiniteHomMatrix.single u t y ∈ cyclotomicIdeal D Sc a n := by
  induction hy using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, w, p, q, rfl⟩ := hf
    by_cases hp : p = 0
    · rw [hp, Limits.zero_comp, FiniteHomMatrix.single_zero]
      exact Submodule.zero_mem _
    let w' : Word I (n + 1) := ⟨j :: w, length_eq_of_hom_ne_zero D Sc n hp⟩
    have e : FiniteHomMatrix.single u t (p ≫ firstDotPoly D Sc a j w ≫ q) =
        FiniteHomMatrix.single u w' (q : wordObj D Sc w' ⟶ wordObj D Sc u) *
          (cyclotomicGenerator D Sc a w' *
            FiniteHomMatrix.single w' t (p : wordObj D Sc t ⟶ wordObj D Sc w')) := by
      rw [cyclotomicGenerator, FiniteHomMatrix.single_mul_single,
        FiniteHomMatrix.single_mul_single, Category.assoc]
      rfl
    rw [e]
    exact Ideal.mul_mem_left _ _ (Submodule.subset_span ⟨w', _, rfl⟩)
  | zero => rw [FiniteHomMatrix.single_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [FiniteHomMatrix.single_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    rw [FiniteHomMatrix.single_smul, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hf

end Matrix

section Descent
variable (a : I → _root_.Polynomial k) (i : I) (n : ℕ) (ε : ZMod 2)
  (N : Type w) [AddCommGroup N] [Module (Hn D Sc (n + 1)) N]

local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))

/-- The elements `y` with `y ψ(1) = y` such that `z y ⊗ m = 0` in `Ind_ψ N` for all `z`, `m`. -/
def appendVanishing : Submodule k (Hn D Sc (n + 1 + 1)) where
  carrier := {y | ∃ hy : y * ψ 1 = y, ∀ (z : Hn D Sc (n + 1 + 1)) (m : N),
    (Ind.tmul ⟨z * y, Ind.mul_mem_of_mul_right hy z⟩ m : Ind N ψ) = 0}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by rw [add_mul, hx, hy], fun z m => ?_⟩
    have e : (⟨z * (x + y), Ind.mul_mem_of_mul_right (by rw [add_mul, hx, hy]) z⟩ :
        InductionAlong.Corner ψ) = ⟨z * x, Ind.mul_mem_of_mul_right hx z⟩ +
          ⟨z * y, Ind.mul_mem_of_mul_right hy z⟩ := Subtype.ext (mul_add _ _ _)
    rw [e, Ind.add_tmul, hx', hy', add_zero]
  zero_mem' := ⟨zero_mul _, fun z m => by
    have e : (⟨z * 0, Ind.mul_mem_of_mul_right (zero_mul _) z⟩ : InductionAlong.Corner ψ) = 0 :=
      Subtype.ext (mul_zero _)
    rw [e, Ind.zero_tmul]⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨by rw [smul_mul_assoc, hx], fun z m => ?_⟩
    have e : (⟨z * (c • x), Ind.mul_mem_of_mul_right (by rw [smul_mul_assoc, hx]) z⟩ :
        InductionAlong.Corner ψ) = ⟨(c • z) * x, Ind.mul_mem_of_mul_right hx _⟩ :=
      Subtype.ext ((mul_smul_comm c z x).trans (smul_mul_assoc c z x).symm)
    rw [e, hx']

variable {a i n ε N}

theorem mul_append_mem_appendVanishing {r : Word I (n + 1 + 1)} (c' : Word I (n + 1))
    (f : wordObj D Sc (appendWord i c') ⟶ wordObj D Sc r) {c : Hn D Sc (n + 1)}
    (hc : ∀ m : N, c • m = 0) :
    FiniteHomMatrix.single r (appendWord i c') f * ψ c ∈ appendVanishing D Sc i n N := by
  have hX := single_mul_appendOne D Sc i n c' f
  refine ⟨by rw [mul_assoc, ← map_mul, mul_one], fun z m => ?_⟩
  exact Ind.tmul_mul_eq_zero hX hc z _ m

/-- The killed part maps into the vanishing elements. -/
theorem single_appendKill_mem (hcyc : ∀ r ∈ cyclotomicIdeal D Sc a n, ∀ m : N, r • m = 0)
    (s t : Word I (n + 1))
    {h : wordObj D Sc (appendWord i t) ⟶ wordObj D Sc (prependWord i s)}
    (hh : h ∈ appendKill D Sc a i t.1 s.1) :
    FiniteHomMatrix.single (prependWord i s) (appendWord i t) h ∈
      appendVanishing D Sc i n N := by
  induction hh using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, y, h', hy, rfl⟩ := hf
    by_cases hy0 : y = 0
    · rw [hy0, MonoidalSupercategory.zero_whiskerRight (R := k), Limits.zero_comp,
        FiniteHomMatrix.single_zero]
      exact Submodule.zero_mem _
    let u' : Word I (n + 1) := ⟨u, length_eq_of_hom_ne_zero D Sc n hy0⟩
    have e : FiniteHomMatrix.single (prependWord i s) (appendWord i t)
          ((y ▷ (pres D Sc).obj (ob D [i])) ≫ h') =
        FiniteHomMatrix.single (prependWord i s) (appendWord i u')
            (h' : wordObj D Sc (appendWord i u') ⟶ wordObj D Sc (prependWord i s)) *
          ψ (FiniteHomMatrix.single u' t (y : wordObj D Sc t ⟶ wordObj D Sc u')) := by
      rw [appendAlgebra_single, FiniteHomMatrix.single_mul_single]
      rfl
    rw [e]
    exact mul_append_mem_appendVanishing D Sc u' _
      (hcyc _ (single_mem_cyclotomicIdeal D Sc a n u' t hy))
  | zero => rw [FiniteHomMatrix.single_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [FiniteHomMatrix.single_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [FiniteHomMatrix.single_smul]; exact Submodule.smul_mem _ c hf

/-- **Matrix form (2)** of `AppendMackeySource.md` §4: `W ψ(c) - φ_ε(c) W` vanishes in
`Ind_ψ N`, for `N` killed by the cyclotomic ideal and by the idempotents of the words `t` with
`q_t ≠ ε`. -/
theorem appendMove_balance_mem (ha : CyclotomicPolynomialParity D a)
    (hcyc : ∀ r ∈ cyclotomicIdeal D Sc a n, ∀ m : N, r • m = 0)
    (hpar : ∀ t : Word I (n + 1), appendQ D a i t.1 ≠ ε →
      ∀ m : N, FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) • m = 0)
    (c : Hn D Sc (n + 1)) :
    appendMoveMatrix D Sc a i n * ψ c - prependTwist D Sc i n ε c * appendMoveMatrix D Sc a i n ∈
      appendVanishing D Sc i n N := by
  induction c using FiniteHomMatrix.induction with
  | hz => rw [map_zero, map_zero, mul_zero, zero_mul, sub_zero]; exact Submodule.zero_mem _
  | ha c c' hc hc' =>
    rw [map_add, map_add, mul_add, add_mul, add_sub_add_comm]
    exact Submodule.add_mem _ hc hc'
  | hs s t g =>
    rw [appendMoveMatrix_mul_append, prependTwist_mul_appendMoveMatrix,
      ← matrix_single_sub]
    by_cases hq : appendQ D a i t.1 = ε
    · subst hq
      exact single_appendKill_mem D Sc hcyc s t (appendError_mem_appendKill D Sc ha g)
    · have e : ∀ f : wordObj D Sc (appendWord i t) ⟶ wordObj D Sc (prependWord i s),
          FiniteHomMatrix.single (prependWord i s) (appendWord i t) f =
            FiniteHomMatrix.single (prependWord i s) (appendWord i t) f *
              ψ (FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t))) := fun f => by
        rw [appendAlgebra_single, FiniteHomMatrix.single_mul_single, appendHom_id,
          Category.id_comp]
      rw [e]
      exact mul_append_mem_appendVanishing D Sc t _ (hpar t hq)

/-- **The append Mackey map** `P : Ind_(φ_ε) N → Ind_ψ N`, `z ⊗ m ↦ z W ⊗ m`
(`AppendMackeySource.md` §4). -/
def appendMackeyMap (ha : CyclotomicPolynomialParity D a)
    (hcyc : ∀ r ∈ cyclotomicIdeal D Sc a n, ∀ m : N, r • m = 0)
    (hpar : ∀ t : Word I (n + 1), appendQ D a i t.1 ≠ ε →
      ∀ m : N, FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) • m = 0) :
    Ind N (prependTwist D Sc i n ε) →ₗ[Hn D Sc (n + 1 + 1)] Ind N ψ :=
  Ind.descend (appendMoveMatrix_mul_appendOne D Sc a i n) fun z c m => by
    obtain ⟨_, hv⟩ := appendMove_balance_mem D Sc (N := N) ha hcyc hpar c
    have h0 := hv z.1 m
    rw [← Ind.op_smul_tmul]
    have e : (⟨z.1 * (appendMoveMatrix D Sc a i n * ψ c -
          prependTwist D Sc i n ε c * appendMoveMatrix D Sc a i n),
          Ind.mul_mem_of_mul_right ‹_› _⟩ : InductionAlong.Corner ψ) =
        MulOpposite.op c • ⟨z.1 * appendMoveMatrix D Sc a i n,
          Ind.mul_mem_of_mul_right (appendMoveMatrix_mul_appendOne D Sc a i n) _⟩ -
        ⟨z.1 * prependTwist D Sc i n ε c * appendMoveMatrix D Sc a i n,
          Ind.mul_mem_of_mul_right (appendMoveMatrix_mul_appendOne D Sc a i n) _⟩ :=
      Subtype.ext (by
        rw [Submodule.coe_sub, InductionAlong.op_smul_val]
        noncomm_ring)
    rw [e, sub_eq_add_neg, Ind.add_tmul, Ind.neg_tmul, add_neg_eq_zero] at h0
    exact h0.symm

@[simp] theorem appendMackeyMap_tmul (ha : CyclotomicPolynomialParity D a)
    (hcyc : ∀ r ∈ cyclotomicIdeal D Sc a n, ∀ m : N, r • m = 0)
    (hpar : ∀ t : Word I (n + 1), appendQ D a i t.1 ≠ ε →
      ∀ m : N, FiniteHomMatrix.single t t (𝟙 (wordObj D Sc t)) • m = 0)
    (z : InductionAlong.Corner (prependTwist D Sc i n ε)) (m : N) :
    appendMackeyMap D Sc ha hcyc hpar (Ind.tmul z m) =
      Ind.tmul ⟨z.1 * appendMoveMatrix D Sc a i n,
        Ind.mul_mem_of_mul_right (appendMoveMatrix_mul_appendOne D Sc a i n) _⟩ m := rfl

end Descent

end OddMath.QuiverHecke
end

end

section

/-!
# Append PBW expansion in the Hom algebra

The expansion terms `c_u x_last^m ψ(b)` of the input-side append decomposition
(the mirror of `PrependCoordinates.lean`, for Kang–Kashiwara–Oh,
arXiv:1206.5933v2, Lemma 8.1), with their right-old-algebra law, corner
membership and matrix entries. `appendPBWTerm_old_nf` identifies a term with a
single old normal form as coefficient with the scalar basis element `appendElt`;
`append_single_expansion` expands every allowed matrix entry. See
`docs/Nondegeneracy/AppendCoordinates.md` §3.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical

/-- Append shuffles for equal block sizes are the same set. -/
def AppendShuffle.cast {n m m' : ℕ} (h : n + 1 = m) (h' : n + 1 = m') :
    AppendShuffle h ≃ AppendShuffle h' := by
  subst h; subst h'; exact Equiv.refl _

theorem AppendShuffle.canWord_cast {n m m' : ℕ} (h : n + 1 = m) (h' : n + 1 = m')
    (u : AppendShuffle h) :
    canWord m' (AppendShuffle.cast h h' u).1⁻¹ = canWord m u.1⁻¹ := by
  subst h; subst h'; rfl

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Moving crossings are indexed independently of the source word. -/
abbrev AppendShuffleAt (n : ℕ) := AppendShuffle (show n + 1 = n + 1 from rfl)

/-- The target word after moving the last strand along an inverse shuffle. -/
def appendShuffleTarget (i : I) {n : ℕ} (u : AppendShuffleAt n) (s : Word I n) :
    Word I (n + 1) :=
  ⟨tgt (s.1 ++ [i]) (cw (canWord (n + 1) u.1⁻¹)), by simp [s.2]⟩

/-- The reduced crossing diagram moving the appended strand. -/
def appendShuffleHom (i : I) {n : ℕ} (u : AppendShuffleAt n) (s : Word I n) :
    wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendShuffleTarget i u s) :=
  cl D Sc (s.1 ++ [i]) _ (cw (canWord (n + 1) u.1⁻¹)) (sChain_pl _ _)

/-- Sum over old words of the moving crossings. -/
def appendShuffleElement (i : I) {n : ℕ} (u : AppendShuffleAt n) : Hn D Sc (n + 1) :=
  ∑ s : Word I n, FiniteHomMatrix.single (appendShuffleTarget i u s) (appendWord i s)
    (appendShuffleHom D Sc i u s)

/-- A coefficient acts first, followed by last-strand dots and the moving crossings. -/
def appendPBWTerm (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (b : Hn D Sc n) : Hn D Sc (n + 1) :=
  appendShuffleElement D Sc i u * affineLastDot D Sc i n ^ m * appendAlgebra D Sc i n b

theorem appendPBWTerm_corner (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (b : Hn D Sc n) :
    appendPBWTerm D Sc i u m b * appendAlgebra D Sc i n 1 = appendPBWTerm D Sc i u m b := by
  simp only [appendPBWTerm, mul_assoc, ← map_mul, mul_one]

/-- The same term as an element of the append induction corner. -/
def appendPBWCorner (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (b : Hn D Sc n) :
    InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) :=
  ⟨appendPBWTerm D Sc i u m b, appendPBWTerm_corner D Sc i u m b⟩

/-! ## Matrix entries -/

theorem affineLastDot_mul_single (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) :
    affineLastDot D Sc i n * FiniteHomMatrix.single (appendWord i t) (appendWord i s) f =
      FiniteHomMatrix.single (appendWord i t) (appendWord i s)
        (f ≫ inductionLastDot D Sc i t) := by
  rw [affineLastDot, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n h)) _ _
  · simp

theorem affineLastDot_pow_mul_single (i : I) {n : ℕ} (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) (m : ℕ) :
    affineLastDot D Sc i n ^ m * FiniteHomMatrix.single (appendWord i t) (appendWord i s) f =
      FiniteHomMatrix.single (appendWord i t) (appendWord i s)
        (f ≫ inductionLastDot D Sc i t ^ m) := by
  induction m with
  | zero => simp [End.one_def]
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, affineLastDot_mul_single]
    congr 1
    rw [pow_succ', End.mul_def, Category.assoc]

theorem appendShuffleElement_mul_single (i : I) {n : ℕ} (u : AppendShuffleAt n)
    (s t : Word I n)
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc (appendWord i t)) :
    appendShuffleElement D Sc i u *
        FiniteHomMatrix.single (appendWord i t) (appendWord i s) f =
      FiniteHomMatrix.single (appendShuffleTarget i u t) (appendWord i s)
        (f ≫ appendShuffleHom D Sc i u t) := by
  rw [appendShuffleElement, Finset.sum_mul, Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    exact FiniteHomMatrix.single_mul_single_of_ne _ _ _ _
      (fun h => hb (appendWord_injective i n h)) _ _
  · simp

/-- The coefficient morphism acts first, then the new dots, then the moving crossing. -/
theorem appendPBWTerm_single (i : I) {n : ℕ} (u : AppendShuffleAt n) (m : ℕ)
    (s t : Word I n) (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    appendPBWTerm D Sc i u m (FiniteHomMatrix.single t s f) =
      FiniteHomMatrix.single (appendShuffleTarget i u t) (appendWord i s)
        (appendHom D Sc i s t f ≫ (inductionLastDot D Sc i t ^ m) ≫
          appendShuffleHom D Sc i u t) := by
  unfold appendPBWTerm
  change (_ * _) * appendLinear D Sc i n (FiniteHomMatrix.single t s f) = _
  rw [appendLinear_single, mul_assoc, affineLastDot_pow_mul_single,
    appendShuffleElement_mul_single, Category.assoc]

omit [Fintype I] in
/-- The last dot is the positioned dot at the last strand. -/
theorem inductionLastDot_eq_dotE (i : I) {n : ℕ} (s : Word I n) :
    inductionLastDot D Sc i s = dotE D Sc (s.1 ++ [i]) s.1.length := by
  simp [inductionLastDot, inductionStrandDot, dotE_eq, cl, wordObj,
    Presentation.diag_whiskerLeft, pl, PG.ld, appendWord]
  exact Presentation.diag_eq_of_layers_eq _
    (by simp [Diagram.whiskerL, mkD, layList, Layer.wl, lay, ob])

/-- The intermediate old target as a word of the original height. -/
def AppendIdx.oldWord {i : I} {s t : List I} (x : AppendIdx i s t) : Word I s.length :=
  ⟨x.oldTarget, by simp [AppendIdx.oldTarget]⟩

/-- The target word has one more strand than the old source. -/
def AppendIdx.targetWord {i : I} {s t : List I} (x : AppendIdx i s t) :
    Word I (s.length + 1) :=
  ⟨t, by rw [← x.moving_target]; simp [AppendIdx.oldTarget]⟩

/-- The moving shuffle of an append index, at the height of its source. -/
def AppendIdx.shuffle {i : I} {s t : List I} (x : AppendIdx i s t) :
    AppendShuffleAt s.length :=
  (AppendShuffle.cast _ _).symm x.1.2.2.2

omit [Fintype I] in
private theorem matrix_single_heq {n : ℕ} {s t t' : Word I n}
    {f : wordObj D Sc s ⟶ wordObj D Sc t} {g : wordObj D Sc s ⟶ wordObj D Sc t'}
    (h : t = t') (hf : HEq f g) :
    FiniteHomMatrix.single t s f = FiniteHomMatrix.single t' s g := by
  subst t'
  cases hf
  rfl

omit [Fintype I] in
private theorem cl_target_heq {s t t' : List I} {l l' : List PG}
    (ht : t = t') (hl : l = l') (h : SChain s (pl s l) t)
    (h' : SChain s (pl s l') t') : HEq (cl D Sc s t l h) (cl D Sc s t' l' h') := by
  subst t'
  subst l'
  rfl

omit [Fintype I] in
theorem AppendIdx.canWord_shuffle {i : I} {s t : List I} (x : AppendIdx i s t) :
    canWord (s.length + 1) x.shuffle.1⁻¹ = canWord (s ++ [i]).length x.1.2.2.2.1⁻¹ := by
  rw [← AppendShuffle.canWord_cast _ (appendLen s i) x.shuffle]
  simp [AppendIdx.shuffle]

/-- A scalar append basis element is exactly the corresponding matrix PBW term. -/
theorem appendPBWTerm_old_nf {i : I} {s t : List I} (x : AppendIdx i s t) :
    appendPBWTerm D Sc i x.shuffle x.1.1
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)) =
    FiniteHomMatrix.single x.targetWord (appendWord i ⟨s, rfl⟩) (appendElt D Sc x) := by
  rw [appendPBWTerm_single, inductionLastDot_eq_dotE, dotE_pow]
  apply matrix_single_heq D Sc (Subtype.ext (by
    simpa only [appendShuffleTarget, AppendIdx.oldWord, AppendIdx.targetWord,
      x.canWord_shuffle] using x.moving_target))
  change HEq ((x.old.nf ▷ (pres D Sc).obj (ob D [i])) ≫ _ ≫ _) _
  rw [nf_whiskerRight]
  unfold appendShuffleHom
  dsimp only [AppendIdx.oldWord, AppendIdx.old]
  rw [cl_comp, cl_comp]
  unfold appendElt
  apply cl_target_heq D Sc (by
    simpa only [appendShuffleTarget, AppendIdx.oldWord, AppendIdx.targetWord,
      x.canWord_shuffle] using x.moving_target)
  simp [AppendIdx.gens, AppendIdx.oldTarget, x.canWord_shuffle, List.append_assoc]

/-- Every allowed matrix entry with appended source has a finite expansion by the
prescribed append PBW terms, with coefficients single old normal forms. -/
theorem append_single_expansion (i : I) (s : List I) (t : Word I (s.length + 1))
    (f : wordObj D Sc (appendWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) :
    FiniteHomMatrix.single t (appendWord i ⟨s, rfl⟩) f =
      ((appendBasis D Sc (i := i) (s := s) (t := t.1)).repr f).sum
        (fun x c => c • appendPBWTerm D Sc i x.shuffle x.1.1
          (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩
            (NFIdx.nf (D := D) (Sc := Sc) x.old))) := by
  let L : (wordObj D Sc (appendWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) →ₗ[k]
      Hn D Sc (s.length + 1) :=
    { toFun := FiniteHomMatrix.single t (appendWord i ⟨s, rfl⟩)
      map_add' := FiniteHomMatrix.single_add _ _
      map_smul' := fun c g => FiniteHomMatrix.single_smul _ _ c g }
  have h := congrArg L ((appendBasis D Sc (i := i) (s := s) (t := t.1)).linearCombination_repr f)
  change L f = _
  rw [← h]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    appendBasis_apply]
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (_ • ·)
  exact (appendPBWTerm_old_nf D Sc x).symm

end OddMath.QuiverHecke
end

end

section

/-!
# Whole affine append-corner coordinates

Mirror of `PrependEquivalence.lean` (KKO I, arXiv:1206.5933v2, Lemma 8.1, for
the append induction): `appendCoordinateEquiv` identifies finite old-algebra
coefficient families with the append corner.
`appendCoefficients_expansion` proves uniqueness using the scalar append
basis and the old normal-form basis. `appendExpansion_projection` proves
existence by finite matrix entries. The forward map is the literal sum of
`appendPBWCorner`; both directions respect the existing right old-algebra
action. Balanced tensor descent and cancellation remain separate steps.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification Categorification.TypeA MonoidalCategory
open scoped Classical
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

/-- Literal finite old-algebra coefficient expansion in the ambient algebra. -/
def appendExpansion (i : I) (n : ℕ) :
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) →ₗ[k] Hn D Sc (n + 1) :=
  Finsupp.lsum k fun q =>
    { toFun := appendPBWTerm D Sc i q.1 q.2
      map_add' := by intros; simp [appendPBWTerm, map_add, mul_add]
      map_smul' := by intros; simp [appendPBWTerm, map_smul] }

@[simp] theorem appendExpansion_single (i : I) (n : ℕ)
    (q : AppendShuffleAt n × ℕ) (b : Hn D Sc n) :
    appendExpansion D Sc i n (Finsupp.single q b) = appendPBWTerm D Sc i q.1 q.2 b :=
  Finsupp.lsum_single _ _ _ _

/-- Regroup one scalar Hom expansion into finite old-algebra coefficients. -/
def appendEntryCoefficients (i : I) (s : List I) (t : Word I (s.length + 1)) :
    (wordObj D Sc (appendWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) →ₗ[k]
      ((AppendShuffleAt s.length × ℕ) →₀ Hn D Sc s.length) :=
  (Finsupp.linearCombination k (fun x : AppendIdx i s t.1 =>
    Finsupp.single (x.shuffle, x.1.1)
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)))).comp
    (appendBasis D Sc (i := i) (s := s) (t := t.1)).repr.toLinearMap

/-- Regrouping retains the single-entry matrix, not merely its span. -/
theorem appendExpansion_entry (i : I) (s : List I) (t : Word I (s.length + 1))
    (f : wordObj D Sc (appendWord i ⟨s, rfl⟩) ⟶ wordObj D Sc t) :
    appendExpansion D Sc i s.length (appendEntryCoefficients D Sc i s t f) =
      FiniteHomMatrix.single t (appendWord i ⟨s, rfl⟩) f := by
  rw [append_single_expansion D Sc i s t f]
  simp [appendEntryCoefficients, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    appendPBWTerm]
  rfl

/-- The same entry regrouping at a fixed height. -/
def appendWordCoefficients (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1)) :
    (wordObj D Sc (appendWord i s) ⟶ wordObj D Sc t) →ₗ[k]
      ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) := by
  rcases s with ⟨s, hs⟩
  subst n
  exact appendEntryCoefficients D Sc i s t

theorem appendExpansion_word (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1))
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc t) :
    appendExpansion D Sc i n (appendWordCoefficients D Sc i s t f) =
      FiniteHomMatrix.single t (appendWord i s) f := by
  rcases s with ⟨s, hs⟩
  subst n
  exact appendExpansion_entry D Sc i s t f

/-- Finite matrix-entry assembly of the old-algebra coefficients. -/
def appendCoefficients (i : I) (n : ℕ) : Hn D Sc (n + 1) →ₗ[k]
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) :=
  ∑ s : Word I n, ∑ t : Word I (n + 1),
    (appendWordCoefficients D Sc i s t).comp
      (DFinsupp.lapply (t, appendWord i s))

/-- Reassembly is the projection onto the allowed columns. -/
theorem appendExpansion_coefficients (i : I) (n : ℕ) (a : Hn D Sc (n + 1)) :
    appendExpansion D Sc i n (appendCoefficients D Sc i n a) =
      ∑ s : Word I n, ∑ t : Word I (n + 1),
        FiniteHomMatrix.single t (appendWord i s) (a (t, appendWord i s)) := by
  simp [appendCoefficients, map_sum, appendExpansion_word]

/-- The old normal form and a chosen shuffle specify one append index. -/
def appendIndex (i : I) {s t : List I} (y : NFIdx s t)
    (q : AppendShuffleAt s.length × ℕ) :
    AppendIdx i s (appendShuffleTarget i q.1 ⟨t, by
      rw [← y.tgt_cw]; simp⟩).1 :=
  ⟨(q.2, y.1.1, y.1.2, AppendShuffle.cast _ (appendLen s i) q.1), y.2.1, y.2.2.1, by
    have he := tgt_append_right [i] (t := s) (fits_cw (validWord_canWord s.length y.1.2))
    simp only [appendCrossingWord, cw_append, tgt_append, he, y.tgt_cw, appendShuffleTarget,
      AppendShuffle.canWord_cast]⟩

theorem appendCoefficients_single (i : I) {n : ℕ} (s : Word I n) (t : Word I (n + 1))
    (f : wordObj D Sc (appendWord i s) ⟶ wordObj D Sc t) :
    appendCoefficients D Sc i n (FiniteHomMatrix.single t (appendWord i s) f) =
      appendWordCoefficients D Sc i s t f := by
  classical
  simp only [appendCoefficients, LinearMap.sum_apply, LinearMap.comp_apply,
    DFinsupp.lapply_apply]
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single t]
    · simp [FiniteHomMatrix.single]
    · intro b _ hb
      simp [FiniteHomMatrix.single, Ne.symm hb]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    have h : appendWord i s ≠ appendWord i b := fun h => hb ((appendWord_injective i n h).symm)
    simp [FiniteHomMatrix.single, h]
  · simp

theorem appendCoefficients_old_nf {i : I} {s t : List I} (x : AppendIdx i s t) :
    appendCoefficients D Sc i s.length
      (appendPBWTerm D Sc i x.shuffle x.1.1
        (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old))) =
    Finsupp.single (x.shuffle, x.1.1)
      (FiniteHomMatrix.single x.oldWord ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) x.old)) := by
  rw [appendPBWTerm_old_nf, appendCoefficients_single]
  change appendEntryCoefficients D Sc i s x.targetWord (appendElt D Sc x) = _
  rw [← appendBasis_apply D Sc x]
  simp only [appendEntryCoefficients, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [Module.Basis.repr_self]
  simp only [Finsupp.linearCombination_single, one_smul]

theorem appendCoefficients_nf (i : I) (s : List I) (t : Word I s.length)
    (y : NFIdx s t.1) (q : AppendShuffleAt s.length × ℕ) :
    appendCoefficients D Sc i s.length
      (appendPBWTerm D Sc i q.1 q.2
        (FiniteHomMatrix.single t ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) y))) =
      Finsupp.single q (FiniteHomMatrix.single t ⟨s, rfl⟩ (NFIdx.nf (D := D) (Sc := Sc) y)) := by
  rcases t with ⟨t, ht⟩
  have he := y.tgt_cw
  rcases y with ⟨⟨L, v⟩, hy⟩
  change tgt s (cw (canWord s.length v)) = t at he
  subst t
  simpa [appendIndex, AppendIdx.oldWord, AppendIdx.old, AppendIdx.oldTarget,
    AppendIdx.shuffle] using
    appendCoefficients_old_nf D Sc (appendIndex i ⟨(L, v), hy⟩ q)

theorem appendCoefficients_term (i : I) {n : ℕ} (q : AppendShuffleAt n × ℕ)
    (b : Hn D Sc n) :
    appendCoefficients D Sc i n (appendPBWTerm D Sc i q.1 q.2 b) = Finsupp.single q b := by
  let P : Hn D Sc n →ₗ[k] Hn D Sc (n + 1) :=
    (appendExpansion D Sc i n).comp (Finsupp.lsingle q)
  rw [← appendExpansion_single D Sc i n q b]
  change appendCoefficients D Sc i n (P b) = Finsupp.single q b
  induction b using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [ha, hb]
  | hs t s f =>
    let E : (wordObj D Sc s ⟶ wordObj D Sc t) →ₗ[k] Hn D Sc n :=
      { toFun := FiniteHomMatrix.single t s
        map_add' := FiniteHomMatrix.single_add _ _
        map_smul' := fun c g => FiniteHomMatrix.single_smul _ _ c g }
    have h : ((appendCoefficients D Sc i n).comp P).comp E =
        (Finsupp.lsingle q).comp E := by
      apply (basisNF D Sc s.1 t.1).ext
      intro y
      simp only [LinearMap.comp_apply, P, Finsupp.lsingle_apply, appendExpansion_single,
        basisNF_apply, E, LinearMap.coe_mk, AddHom.coe_mk]
      rcases s with ⟨s, hs⟩
      subst n
      exact appendCoefficients_nf D Sc i s t y q
    exact LinearMap.congr_fun h f

/-- Scalar append independence recovers every old-algebra coefficient. -/
theorem appendCoefficients_expansion (i : I) (n : ℕ)
    (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) :
    appendCoefficients D Sc i n (appendExpansion D Sc i n b) = b := by
  have h : (appendCoefficients D Sc i n).comp (appendExpansion D Sc i n) =
      LinearMap.id := by
    apply Finsupp.lhom_ext
    intro q b
    simpa only [LinearMap.comp_apply, appendExpansion_single, LinearMap.id_apply] using
      appendCoefficients_term D Sc i q b
  exact LinearMap.congr_fun h b

/-- Uniqueness holds for coefficients in the whole old algebra. -/
theorem appendExpansion_injective (i : I) (n : ℕ) :
    Function.Injective (appendExpansion D Sc i n) :=
  Function.LeftInverse.injective (appendCoefficients_expansion D Sc i n)

private theorem matrix_mul_idem_sum {n : ℕ} (a : Hn D Sc n) (s : Word I n) :
    a * FiniteHomMatrix.idem s =
      ∑ t : Word I n, FiniteHomMatrix.single t s (a (t, s)) := by
  classical
  induction a using FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp [add_mul, ha, hb, DFinsupp.add_apply,
      Finset.sum_add_distrib]
  | hs t r f =>
    by_cases h : r = s
    · subst r
      rw [FiniteHomMatrix.single_mul_idem]
      symm
      rw [Finset.sum_eq_single t]
      · simp [FiniteHomMatrix.single]
      · intro b _ hb
        simp [FiniteHomMatrix.single, Ne.symm hb]
      · simp
    · rw [FiniteHomMatrix.idem, FiniteHomMatrix.single_mul_single_of_ne _ _ _ _ h]
      symm
      apply Finset.sum_eq_zero
      intro b _
      simp [FiniteHomMatrix.single, h]

/-- The matrix reassembly is multiplication by the append idempotent. -/
theorem appendExpansion_projection (i : I) (n : ℕ) (a : Hn D Sc (n + 1)) :
    appendExpansion D Sc i n (appendCoefficients D Sc i n a) =
      a * appendAlgebra D Sc i n 1 := by
  rw [appendExpansion_coefficients]
  change _ = a * appendLinear D Sc i n (FiniteHomMatrix.localUnit Finset.univ)
  simp only [FiniteHomMatrix.localUnit, map_sum, FiniteHomMatrix.idem, appendLinear_single,
    appendHom, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  erw [MonoidalSupercategory.id_whiskerRight (R := k)]
  exact (matrix_mul_idem_sum D Sc a (appendWord i s)).symm

/-- Every element of the whole corner has finite old-algebra coefficients. -/
theorem appendExpansion_exists (i : I) (n : ℕ)
    (z : InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    ∃ b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n, appendExpansion D Sc i n b = z.1 :=
  ⟨appendCoefficients D Sc i n z.1, (appendExpansion_projection D Sc i n z.1).trans z.2⟩

/-- The finite expansion lands in the corner. -/
def appendCornerExpansion (i : I) (n : ℕ) :
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) →ₗ[k]
      InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) where
  toFun b := ⟨appendExpansion D Sc i n b, by
    have h := appendExpansion_projection D Sc i n (appendExpansion D Sc i n b)
    rw [appendCoefficients_expansion] at h
    exact h.symm⟩
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' c b := Subtype.ext (map_smul _ c b)

/-- Whole affine append-corner coordinates (mirror of KKO I, Lemma 8.1). -/
def appendCoordinateEquiv (i : I) (n : ℕ) :
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) ≃ₗ[k]
      InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1)) :=
  LinearEquiv.ofBijective (appendCornerExpansion D Sc i n) ⟨
    fun a b h => appendExpansion_injective D Sc i n (congrArg Subtype.val h), by
      intro z
      obtain ⟨b, hb⟩ := appendExpansion_exists D Sc i n z
      exact ⟨b, Subtype.ext hb⟩⟩

/-- Forward coordinates are the literal finite sum of append corner terms. -/
theorem appendCoordinateEquiv_apply (i : I) (n : ℕ)
    (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) :
    appendCoordinateEquiv D Sc i n b =
      b.sum (fun q c => appendPBWCorner D Sc i q.1 q.2 c) := by
  apply Subtype.ext
  change appendExpansion D Sc i n b = _
  simp [appendExpansion, Finsupp.lsum_apply, Finsupp.sum, appendPBWCorner]

/-- The inverse is the finite entrywise coefficient assembly. -/
theorem appendCoordinateEquiv_symm_apply (i : I) (n : ℕ)
    (z : InductionAlong.Corner (appendAlgebra D Sc i n : Hn D Sc n →ₙ+* Hn D Sc (n + 1))) :
    (appendCoordinateEquiv D Sc i n).symm z = appendCoefficients D Sc i n z.1 := by
  apply (appendCoordinateEquiv D Sc i n).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  exact ((appendExpansion_projection D Sc i n z.1).trans z.2).symm

/-- Coefficientwise right multiplication by an old-algebra element. -/
def appendRightCoefficients {n : ℕ} (r : Hn D Sc n) :
    ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) →ₗ[k]
      ((AppendShuffleAt n × ℕ) →₀ Hn D Sc n) :=
  Finsupp.mapRange.linearMap
    { toFun := fun b => b * r
      map_add' := fun a b => add_mul a b r
      map_smul' := fun c b => smul_mul_assoc c b r }

@[simp] theorem appendRightCoefficients_apply {n : ℕ} (r : Hn D Sc n)
    (b : (AppendShuffleAt n × ℕ) →₀ Hn D Sc n) (q : AppendShuffleAt n × ℕ) :
    appendRightCoefficients D Sc r b q = b q * r := rfl

end OddMath.QuiverHecke
end

end
