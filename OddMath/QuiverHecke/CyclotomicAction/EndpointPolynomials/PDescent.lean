import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Algebra.Polynomial.Monic
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance.SignedAppendBalance
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwiner
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.FiniteHomMatrixRightModule

/-!
# Endpoint polynomials

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Descent of the full ELV old-generator map

Precomposition by the prescribed crossing word followed by the full ELV relation
maps the prepend-old relation span into the append-old relation span. This gives
P between the two old-only quotients. No injectivity, exactness, or polynomial
module linearity is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed morphism carries an inserted old ideal element into the append span. -/
theorem appendW_insert_ideal (i : I) {v t : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t) :
    appendW D Sc cutoff i v ≫ insert D Sc cutoff i v t r ∈
      appendRelations D Sc cutoff i v (i :: t) := by
  have he := appendError_mem_appendRelations D Sc cutoff i
    (twist k (appendQ D cutoff i v) r)
  rw [appendError_apply, twist_twist] at he
  have hi := appendRelations_mem D Sc cutoff i
    (twist_ideal D Sc cutoff (appendQ D cutoff i v) hr) (appendW D Sc cutoff i t)
  have h := Submodule.sub_mem (appendRelations D Sc cutoff i v (i :: t)) hi he
  simpa only [sub_sub_cancel] using h

/-- All old composites and ambient continuations are respected by the prescribed map. -/
theorem appendW_relations (i : I) {v w : List I}
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    appendW D Sc cutoff i v ≫ h ∈ appendRelations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, a, rfl⟩ := hh
    rw [← Category.assoc]
    exact appendRelations_comp D Sc cutoff i (appendW_insert_ideal D Sc cutoff i hr) a
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Preadditive.comp_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [Linear.comp_smul]
    exact Submodule.smul_mem _ c ha

/-- P on old-only quotient coordinates, with the prescribed W and no balance hypothesis. -/
def pMap (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] AppendTarget D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (appendRelations D Sc cutoff i v w)
    (Linear.leftComp k _ (appendW D Sc cutoff i v))
    (fun _ hh => appendW_relations D Sc cutoff i hh)

/-- The descended map is precomposition by W, not an unspecified quotient lift. -/
@[simp] theorem pMap_projection (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w) :
    pMap D Sc cutoff i v w (projection D Sc cutoff i v w h) =
      appendProjection D Sc cutoff i v w
        ((affineUnit D Sc cutoff (v ++ [i]) (i :: v) (lastToFirstHom D Sc i v) ≫
          relation D Sc cutoff i v) ≫ h) := rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Ordinary old ELV quotient category

The old cyclotomic Hom quotients form a linear category. Its finite content
Hom matrices give the ordinary coefficient ring in the square resolution.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Words in the old cyclotomic ELV category. -/
structure OldCategory (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (cutoff : I → ℕ) where
  word : List I

/-- Quotient composition, in categorical order. -/
def oldComp (v t w : List I) :
    Old D Sc cutoff v t →ₗ[k]
      Old D Sc cutoff t w →ₗ[k] Old D Sc cutoff v w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun f =>
        { toFun := fun g => (ideal D Sc cutoff v w).mkQ (f ≫ g)
          map_add' := by intros; simp only [Preadditive.comp_add, map_add]
          map_smul' := by intros; simp only [Linear.comp_smul, map_smul, RingHom.id_apply] }
       map_add' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Preadditive.add_comp, map_add, LinearMap.add_apply]
       map_smul' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Linear.smul_comp, map_smul, LinearMap.smul_apply, RingHom.id_apply] } :
       hom D Sc cutoff v t →ₗ[k] hom D Sc cutoff t w →ₗ[k] Old D Sc cutoff v w)
    (by
      intro f hf
      ext g
      exact (Submodule.Quotient.mk_eq_zero _).mpr (ideal_comp D Sc cutoff hf g))
    (by
      intro g hg
      ext f
      exact (Submodule.Quotient.mk_eq_zero _).mpr (comp_ideal D Sc cutoff f hg))

@[simp] theorem oldComp_mk (v t w : List I)
    (f : hom D Sc cutoff v t) (g : hom D Sc cutoff t w) :
    oldComp D Sc cutoff v t w
      ((ideal D Sc cutoff v t).mkQ f)
      ((ideal D Sc cutoff t w).mkQ g) =
      (ideal D Sc cutoff v w).mkQ (f ≫ g) := rfl

instance oldCategory : Category (OldCategory D Sc cutoff) where
  Hom v w := Old D Sc cutoff v.word w.word
  id v := (ideal D Sc cutoff v.word v.word).mkQ (𝟙 _)
  comp {v t w} f g := oldComp D Sc cutoff v.word t.word w.word f g
  id_comp := by
    intro v w f
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
    exact congrArg (ideal D Sc cutoff v.word w.word).mkQ (Category.id_comp f)
  comp_id := by
    intro v w f
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
    exact congrArg (ideal D Sc cutoff v.word w.word).mkQ (Category.comp_id f)
  assoc := by
    intro v t w z f g h
    obtain ⟨f, rfl⟩ := (ideal D Sc cutoff v.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff t.word w.word).mkQ_surjective g
    obtain ⟨h, rfl⟩ := (ideal D Sc cutoff w.word z.word).mkQ_surjective h
    exact congrArg (ideal D Sc cutoff v.word z.word).mkQ (Category.assoc f g h)

instance oldPreadditive : Preadditive (OldCategory D Sc cutoff) where
  homGroup v w := inferInstanceAs (AddCommGroup (Old D Sc cutoff v.word w.word))
  add_comp := by
    intro v t w f g h
    exact LinearMap.map_add₂ (oldComp D Sc cutoff v.word t.word w.word) f g h
  comp_add := by
    intro v t w f g h
    exact (oldComp D Sc cutoff v.word t.word w.word f).map_add g h

instance oldLinear : Linear k (OldCategory D Sc cutoff) where
  homModule v w := inferInstanceAs (Module k (Old D Sc cutoff v.word w.word))
  smul_comp := by
    intro v t w r f g
    exact LinearMap.map_smul₂ (oldComp D Sc cutoff v.word t.word w.word) r f g
  comp_smul := by
    intro v t w f r g
    exact (oldComp D Sc cutoff v.word t.word w.word f).map_smul r g

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Regularity of the signed QP product

The actual factors have invertible highest moving coefficients. Finite moving
support in the old-only quotient proves cancellation factor by factor, retaining
the total old-coefficient parity involution and the repeated-even minus signs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldSource_movingPower_above (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (c : hom D Sc cutoff v v)
    (f : PrependOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    prependOldCoordinate D Sc cutoff p x
      (oldSourceTarget D Sc cutoff i v w c
        (signedMovingPowerTarget D Sc cutoff i v w d
          (prependOldReconstruct D Sc cutoff p i v w f))) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift,
    oldSourceTarget_pair]
  apply prependOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega

theorem affineUnit_dotPower (v : List I) (b d : ℕ) :
    affineUnit D Sc cutoff v v (dotE D Sc v b ^ d) =
      sourceDotPower D Sc cutoff v b d := rfl

theorem projection_moving_dotPower (i : I) (v w : List I) (d : ℕ)
    (h : hom D Sc cutoff (i :: v) w) :
    projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ d) ≫ h) =
      signedMovingPowerTarget D Sc cutoff i v w d (projection D Sc cutoff i v w h) := rfl

theorem projection_old_dotPower (i : I) (v w : List I) (b d : ℕ)
    (h : hom D Sc cutoff (i :: v) w) :
    projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) (b + 1) ^ d) ≫ h) =
      oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b d)
        (projection D Sc cutoff i v w h) := by
  rw [oldSourceTarget_projection, insert_sourceDotPower, affineUnit_dotPower]

/-- The linear moving difference is regular even when its moving dot is odd. -/
theorem projection_dotDifference_regular (i : I) (v w : List I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (dotE D Sc (i :: v) (b + 1) - dotE D Sc (i :: v) 0) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  let z := projection D Sc cutoff i v w h
  let f := prependOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have hb : ∀ t ∈ f.support, t.1.1 < (q.representative.shift 1).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change t.1.1 < 1 + q.representative.1.1
    omega
  rw [map_sub, Preadditive.sub_comp, map_sub] at hh
  have hp : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) (b + 1)) ≫ h) =
      oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b 1) z := by
    simpa only [pow_one] using projection_old_dotPower D Sc cutoff i v w b 1 h
  have hm : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0) ≫ h) =
      signedMovingPowerTarget D Sc cutoff i v w 1 z := by
    simpa only [pow_one] using projection_moving_dotPower D Sc cutoff i v w 1 h
  rw [hp, hm] at hh
  change oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b 1) z -
    signedMovingPowerTarget D Sc cutoff i v w 1 z = 0 at hh
  have he := congrArg (prependOldCoordinate D Sc cutoff 0 (q.representative.shift 1)) hh
  rw [map_sub, map_zero, signedMovingPower_coordinate] at he
  have ho := oldSourceTarget_above D Sc cutoff 0 (q.representative.shift 1)
    (sourceDotPower D Sc cutoff v b 1) f hb
  rw [prependOldReconstruct_coordinateEquiv] at ho
  rw [ho, zero_sub, neg_eq_zero] at he
  have hh' := congrArg (oldTwist D Sc cutoff (1 • D.parity i) v q.representative.oldTarget) he
  rw [oldTwist_twice, map_zero] at hh'
  exact (DFinsupp.mem_support_iff.mp hq) hh'

/-- The prescribed distinct-colour factor has the unit `t i x` as highest moving coefficient. -/
theorem projection_qPoly_regular (i x : I) (hix : i ≠ x) (v w : List I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        (qPoly D Sc (dotE D Sc (i :: v) 0) (dotE D Sc (i :: v) (b + 1)) i x) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  by_cases hd : D.d i x = 0
  · rw [qPoly, ite_eq_left hd, map_smul, End.one_def, affineUnit_id,
      Linear.smul_comp, Category.id_comp, map_smul] at hh
    exact (Sc.t i x).isUnit.smul_eq_zero.mp hh
  let z := projection D Sc cutoff i v w h
  let f := prependOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have hpos : 0 < D.dn i x := by
    have hc := D.dn_cast hix
    omega
  have hb (d : ℕ) (hlt : d < D.dn i x) :
      ∀ t ∈ f.support, d + t.1.1 < (q.representative.shift (D.dn i x)).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change d + t.1.1 < D.dn i x + q.representative.1.1
    omega
  have hlow (d e : ℕ) (hlt : d < D.dn i x) :
      prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))
        (projection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (i :: v) 0 ^ d * dotE D Sc (i :: v) (b + 1) ^ e) ≫ h)) = 0 := by
    rw [End.mul_def, affineUnit_comp, Category.assoc, projection_old_dotPower,
      projection_moving_dotPower]
    simpa only [f, prependOldReconstruct_coordinateEquiv] using
      oldSource_movingPower_above D Sc cutoff 0 (q.representative.shift (D.dn i x))
        d (sourceDotPower D Sc cutoff v b e) f (hb d hlt)
  have hold : prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))
      (projection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) (b + 1) ^ D.dn x i) ≫ h)) = 0 := by
    simpa only [pow_zero, one_mul] using hlow 0 (D.dn x i) hpos
  rw [qPoly, ite_eq_right hd, map_add, map_add, Preadditive.add_comp,
    Preadditive.add_comp, map_add, map_add] at hh
  have he := congrArg (prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))) hh
  simp only [map_add, map_zero, map_sum, Preadditive.sum_comp, map_smul,
    Linear.smul_comp] at he
  have hl : (∑ d ∈ Finset.range (D.dn i x), ∑ e ∈ Finset.range (D.dn x i),
      Sc.s i x d e • prependOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i x))
        (projection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (i :: v) 0 ^ d * dotE D Sc (i :: v) (b + 1) ^ e) ≫ h))) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd'
    apply Finset.sum_eq_zero
    intro e _
    rw [hlow d e (Finset.mem_range.mp hd'), smul_zero]
  rw [hl, hold, smul_zero, add_zero, zero_add, projection_moving_dotPower,
    signedMovingPower_coordinate] at he
  have ht := (Sc.t i x).isUnit.smul_eq_zero.mp he
  have ht' := congrArg (oldTwist D Sc cutoff (D.dn i x • D.parity i) v q.representative.oldTarget) ht
  rw [oldTwist_twice, map_zero] at ht'
  exact (DFinsupp.mem_support_iff.mp hq) ht'

/-- Every actual signed QP factor cancels in the old-only quotient. -/
theorem projection_qpFactor_regular (i : I) (v w : List I) (x : I) (b : ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpFactor D Sc i v x b) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  unfold qpFactor at hh
  split_ifs at hh with hx hi
  · rw [pow_two, End.mul_def, affineUnit_comp, Category.assoc] at hh
    exact projection_dotDifference_regular D Sc cutoff i v w b h
      (projection_dotDifference_regular D Sc cutoff i v w b _ hh)
  · rw [map_neg, End.one_def, affineUnit_id, Preadditive.neg_comp,
      Category.id_comp, map_neg, neg_eq_zero] at hh
    exact hh
  · exact projection_qPoly_regular D Sc cutoff i x (Ne.symm hx) v w b h hh

/-- Cancellation for a list of the prescribed factors, in their actual multiplication order. -/
theorem projection_qpFactorList_regular (i : I) (v w : List I) (l : List ℕ)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _
        ((l.map fun b => qpFactor D Sc i v (v.getD b i) b).prod) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  induction l generalizing h with
  | nil => simpa only [List.map_nil, List.prod_nil, End.one_def, affineUnit_id,
      Category.id_comp] using hh
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons, End.mul_def, affineUnit_comp, Category.assoc] at hh
    exact projection_qpFactor_regular D Sc cutoff i v w (v.getD b i) b h (ih _ hh)

/-- The signed all-word product is regular, without assuming any monicity or support bound. -/
theorem projection_qpProduct_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 :=
  projection_qpFactorList_regular D Sc cutoff i v w (List.range v.length) h hh

/-- Actual full-ELV QP regularity in diagram composition order.
This is the raw-quotient injectivity input to the deformed square resolution;
it does not assume that the displayed operation descends to an endomorphism. -/
theorem projection_qp_relation_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i v) ≫
        relation D Sc cutoff i v ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 :=
  projection_relation_regular D Sc cutoff i v w h
    (projection_qpProduct_regular D Sc cutoff i v w _ hh)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Monic normalized endpoint norm polynomials

The independent moving-chain norm factors have the prescribed scalar unit leading
coefficients over any possibly noncommutative coefficient ring. Their ordered
normalized product is monic. `EndpointNormEvaluation` evaluates this polynomial
on actual affine dots; neither norm cancellation in a cyclotomic quotient nor
bounded cyclotomic support is inferred from monicity alone.
-/

noncomputable section
open scoped Classical
open Polynomial
namespace OddMath.QuiverHecke
open IntertwinerMeet
universe u v
variable {I k : Type u} {L : Type v} [AddCommGroup L]
  (D : SKM.Datum I L) [CommRing k] (Sc : SKM.Scalars D k)
variable {B : Type*} [Ring B] [Algebra k B]

theorem qLeft_polynomial_leadingCoeff (u : B) (d e : ℕ) (he : 0 < e)
    (t₁ : k) (t₂ : kˣ) (s : ℕ → ℕ → k) :
    (qLeft (C u) (X : Polynomial B) d e t₁ (t₂ : k) s).leadingCoeff =
      algebraMap k B (t₂ : k) := by
  nontriviality B
  have ht : algebraMap k B (t₂ : k) ≠ 0 := (t₂.isUnit.map (algebraMap k B)).ne_zero
  have hlow : (∑ p ∈ Finset.range d, ∑ q ∈ Finset.range e,
      s p q • ((C u : Polynomial B) ^ p * X ^ q)).degree < (e : WithBot ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (by simp)).mpr
    intro p hp
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (by simp)).mpr
    intro q hq
    apply lt_of_le_of_lt (degree_smul_le _ _)
    rw [← map_pow]
    exact (degree_C_mul_X_pow_le q (u ^ p)).trans_lt
      (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hq))
  have hconst : ((t₁ • (C u : Polynomial B) ^ d)).degree < (e : WithBot ℕ) := by
    apply lt_of_le_of_lt (degree_smul_le _ _)
    rw [← map_pow]
    exact degree_C_le.trans_lt (WithBot.coe_lt_coe.mpr he)
  have htop : (t₂.val • (X : Polynomial B) ^ e) =
      C (algebraMap k B t₂.val) * X ^ e := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  unfold qLeft
  rw [← add_assoc, htop, leadingCoeff_add_of_degree_lt]
  · simp
  · rw [degree_C_mul_X_pow e ht]
    exact (degree_add_le _ _).trans_lt (max_lt hlow hconst)

/-- The literal leading scalar: diagonal minus sign, or the appropriate t unit. -/
def endpointNormLeadingUnit (j i : I) : kˣ :=
  if j = i then -1 else if D.d j i = 0 then Sc.t j i else Sc.t i j

theorem endpointNormFactor_polynomial_leadingCoeff (j i : I) (u : B) :
    (endpointNormFactor D Sc j i (C u) (X : Polynomial B)).leadingCoeff =
      algebraMap k B (endpointNormLeadingUnit D Sc j i : k) := by
  unfold endpointNormFactor endpointNormLeadingUnit
  split_ifs with hji hp hd
  · have hm : (((X : Polynomial B) ^ 2 - C u ^ 2) ^ 2 *
        (C u ^ 2 + X ^ 2)).Monic := by
      apply Monic.mul
      · apply Monic.pow
        simpa only [← map_pow] using
          (monic_X_pow_sub_C (u ^ 2) (by decide : (2 : ℕ) ≠ 0))
      · simpa only [← map_pow, add_comm] using
          (monic_X_pow_add_C (u ^ 2) (by decide : (2 : ℕ) ≠ 0))
    simp [leadingCoeff_neg, hm.leadingCoeff]
  · have hm : (((X : Polynomial B) - C u) ^ 2).Monic :=
      (monic_X_sub_C u).pow 2
    simp [leadingCoeff_neg, hm.leadingCoeff]
  · simp only [Polynomial.algebraMap_apply, leadingCoeff_C]
  · have he : 0 < D.dn i j := by
      have hc := D.dn_cast (Ne.symm hji)
      have hz : D.d i j ≠ 0 := fun hz => hd ((D.d_eq_zero_iff j i).mpr hz)
      omega
    exact qLeft_polynomial_leadingCoeff u _ _ he _ _ _

/-- Left normalization by the explicit inverse sign/t unit. -/
def normalizedEndpointNormFactor (j i : I) (u : B) : Polynomial B :=
  C (algebraMap k B ((endpointNormLeadingUnit D Sc j i)⁻¹ : kˣ)) *
    endpointNormFactor D Sc j i (C u) X

theorem normalizedEndpointNormFactor_monic (j i : I) (u : B) :
    (normalizedEndpointNormFactor D Sc j i u).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [endpointNormFactor_polynomial_leadingCoeff, ← map_mul]
  simp

/-- Ordered normalized product; no commutativity of the coefficient ring is used. -/
def normalizedEndpointNormPolynomial (i : I) : List (I × B) → Polynomial B
  | [] => 1
  | (j, u) :: xs => normalizedEndpointNormFactor D Sc j i u *
      normalizedEndpointNormPolynomial i xs

theorem normalizedEndpointNormPolynomial_monic (i : I) (xs : List (I × B)) :
    (normalizedEndpointNormPolynomial D Sc i xs).Monic := by
  induction xs with
  | nil => exact monic_one
  | cons x xs ih =>
    exact (normalizedEndpointNormFactor_monic D Sc x.1 i x.2).mul ih

end OddMath.QuiverHecke
end

end

section

/-! # Evaluation of the ordered monic endpoint norm

Parity-supported old-dot powers commute with the moving dot even when the
individual dots do not. Evaluation therefore recovers the independent chain
norm times its explicit inverse leading unit, for arbitrary words.
-/
noncomputable section
namespace OddMath.QuiverHecke
open Polynomial IntertwinerMeet
universe u v
variable {I k : Type u} {L : Type v} [AddCommGroup L]
  (D : SKM.Datum I L) [CommRing k] (Sc : SKM.Scalars D k)
variable {B : Type*} [Ring B] [Algebra k B]

def NormCoeffCommute (x : B) (p : Polynomial B) : Prop :=
  ∀ n, Commute (p.coeff n) x

namespace NormCoeffCommute
variable {x : B} {p q : Polynomial B}
theorem const {a : B} (h : Commute a x) : NormCoeffCommute x (C a) := by
  intro n
  by_cases hn : n = 0 <;> simp [coeff_C, hn, h]
theorem X : NormCoeffCommute x (Polynomial.X : Polynomial B) := by
  intro n
  by_cases hn : 1 = n <;> simp [coeff_X, hn]
theorem add (hp : NormCoeffCommute x p) (hq : NormCoeffCommute x q) :
    NormCoeffCommute x (p + q) := by
  intro n
  simpa using (hp n).add_left (hq n)
theorem neg (hp : NormCoeffCommute x p) : NormCoeffCommute x (-p) := by
  intro n
  simpa using (hp n).neg_left
theorem sub (hp : NormCoeffCommute x p) (hq : NormCoeffCommute x q) :
    NormCoeffCommute x (p - q) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg
theorem mul (hp : NormCoeffCommute x p) (hq : NormCoeffCommute x q) :
    NormCoeffCommute x (p * q) := by
  intro n
  rw [coeff_mul]
  apply Commute.sum_left
  intro a ha
  exact (hp a.1).mul_left (hq a.2)
theorem pow (hp : NormCoeffCommute x p) (n : ℕ) : NormCoeffCommute x (p ^ n) := by
  induction n with
  | zero => simpa using (const (Commute.one_left x))
  | succ n ih => simpa only [pow_succ] using ih.mul hp
theorem eval_mul (hq : NormCoeffCommute x q) :
    (p * q).eval₂ (RingHom.id B) x =
      p.eval₂ (RingHom.id B) x * q.eval₂ (RingHom.id B) x :=
  eval₂_mul_noncomm _ _ hq
theorem eval_pow (hp : NormCoeffCommute x p) (n : ℕ) :
    (p ^ n).eval₂ (RingHom.id B) x = (p.eval₂ (RingHom.id B) x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, hp.eval_mul, ih, pow_succ]
end NormCoeffCommute

theorem eval₂_qLeft (u x : B) (d e : ℕ) (t₁ t₂ : k) (s : ℕ → ℕ → k) :
    (qLeft (C u) (X : Polynomial B) d e t₁ t₂ s).eval₂ (RingHom.id B) x =
      qLeft u x d e t₁ t₂ s := by
  have hx : (X ^ e : Polynomial B).eval x = x ^ e := eval₂_X_pow _ _
  simp [qLeft, eval₂_finsetSum, ← map_pow, hx]

theorem eval₂_endpointNormFactor (j i : I) (u x : B)
    (hodd : Commute (u ^ 2) x) (heven : D.parity j ≠ 1 → Commute u x) :
    (endpointNormFactor D Sc j i (C u) (X : Polynomial B)).eval₂ (RingHom.id B) x =
      endpointNormFactor D Sc j i u x := by
  unfold endpointNormFactor
  split_ifs with hji hp hd
  · have hc : NormCoeffCommute x ((C u : Polynomial B) ^ 2) := by
      simpa only [← map_pow] using NormCoeffCommute.const hodd
    have hx := (NormCoeffCommute.X (x := x)).pow 2
    rw [eval₂_neg, (hc.add hx).eval_mul, (hx.sub hc).eval_pow]
    simp [← map_pow]
  · rw [eval₂_neg, ((NormCoeffCommute.X (x := x)).sub
      (NormCoeffCommute.const (heven hp))).eval_pow]
    simp
  · simp [Polynomial.algebraMap_apply]
  · exact eval₂_qLeft u x _ _ _ _ _

theorem eval₂_normalizedEndpointNormFactor (j i : I) (u x : B)
    (hodd : Commute (u ^ 2) x) (heven : D.parity j ≠ 1 → Commute u x) :
    (normalizedEndpointNormFactor D Sc j i u).eval₂ (RingHom.id B) x =
      algebraMap k B ((endpointNormLeadingUnit D Sc j i)⁻¹ : kˣ) *
        endpointNormFactor D Sc j i u x := by
  unfold normalizedEndpointNormFactor
  rw [← Polynomial.algebraMap_apply, ← Algebra.smul_def, eval₂_id, eval_smul, ← eval₂_id,
    eval₂_endpointNormFactor D Sc j i u x hodd heven, Algebra.smul_def]

theorem NormCoeffCommute.smul {x : B} {p : Polynomial B}
    (hp : NormCoeffCommute x p) (a : k) : NormCoeffCommute x (a • p) := by
  intro n
  change Commute (a • p.coeff n) x
  rw [Algebra.smul_def]
  exact (Algebra.commute_algebraMap_left a x).mul_left (hp n)

theorem NormCoeffCommute.sum {x : B} {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial B) (h : ∀ a ∈ s, NormCoeffCommute x (f a)) :
    NormCoeffCommute x (∑ a ∈ s, f a) := by
  intro n
  rw [finsetSum_coeff]
  apply Commute.sum_left
  intro a ha
  exact h a ha n

theorem endpointNormFactor_coeffCommute (j i : I) (u x : B)
    (hpow : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 → Commute (u ^ n) x) :
    NormCoeffCommute x (endpointNormFactor D Sc j i (C u) (X : Polynomial B)) := by
  have hc (n : ℕ) (hn : (n : ZMod 2) * D.parity j = 0) :
      NormCoeffCommute x ((C u : Polynomial B) ^ n) := by
    simpa only [← map_pow] using NormCoeffCommute.const (hpow n hn)
  have hx := NormCoeffCommute.X (x := x)
  unfold endpointNormFactor
  split_ifs with hji hp hd
  · have hc2 := hc 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul])
    exact (((hx.pow 2).sub hc2).pow 2 |>.mul (hc2.add (hx.pow 2))).neg
  · have hc1 : NormCoeffCommute x (C u) := by
      simpa using hc 1 (by rw [parity_eq_zero_of_ne_one hp, mul_zero])
    exact ((hx.sub hc1).pow 2).neg
  · rw [Polynomial.algebraMap_apply]
    exact NormCoeffCommute.const (Algebra.commutes _ _)
  · unfold qLeft
    apply NormCoeffCommute.add
    · apply NormCoeffCommute.sum
      intro p hp
      apply NormCoeffCommute.sum
      intro q hq
      by_cases hs : Sc.s j i p q = 0
      · simp only [hs, zero_smul]
        simpa using (NormCoeffCommute.const (Commute.zero_left x))
      · apply NormCoeffCommute.smul
        apply NormCoeffCommute.mul _ (hx.pow q)
        exact hc p (zmod_two_eq_zero_of_ne_one fun h => hs (Sc.s_eq_zero j i p q h))
    · exact ((hc _ (dn_mul_parity D j i)).smul _).add ((hx.pow _).smul _)

theorem normalizedEndpointNormFactor_coeffCommute (j i : I) (u x : B)
    (hpow : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 → Commute (u ^ n) x) :
    NormCoeffCommute x (normalizedEndpointNormFactor D Sc j i u) := by
  exact (NormCoeffCommute.const (Algebra.commutes _ _)).mul
    (endpointNormFactor_coeffCommute D Sc j i u x hpow)

theorem norm_mul_pow_signed (a b : B) (e : k) (h : a * b = e • (b * a))
    (n : ℕ) : a * b ^ n = e ^ n • (b ^ n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h,
      mul_smul_comm, ← mul_assoc, smul_smul, ← pow_succ, ← pow_succ]

open CategoryTheory in
theorem norm_oldDot_pow_commute (l m : List I) (j i : I) (n : ℕ)
    (hn : (n : ZMod 2) * D.parity j = 0) :
    Commute (dotE D Sc (l ++ [j] ++ m ++ [i]) l.length ^ n)
      (dotE D Sc (l ++ [j] ++ m ++ [i]) (l.length + 1 + m.length)) := by
  have hs := genE_interchange D Sc l m [] (.dot j) (.dot i) rfl rfl
    (w := l ++ [j] ++ m ++ [i]) (by simp [Shape.dom]) (p := l.length)
    (q := l.length + 1 + m.length) rfl (by simp only [Shape.dom, List.length_append, List.length_singleton])
  simp only [Shape.parity, PG.ofShape] at hs
  have h := norm_mul_pow_signed _ _ _ hs n
  rw [zsign_pow, ← mul_assoc, hn, zero_mul] at h
  simp [SKM.zsign] at h
  exact h.symm

theorem normalizedEndpointNormPolynomial_coeffCommute (i : I) (xs : List (I × B)) (x : B)
    (h : ∀ z ∈ xs, ∀ n : ℕ, (n : ZMod 2) * D.parity z.1 = 0 → Commute (z.2 ^ n) x) :
    NormCoeffCommute x (normalizedEndpointNormPolynomial D Sc i xs) := by
  induction xs with
  | nil => exact NormCoeffCommute.const (Commute.one_left x)
  | cons z zs ih =>
    exact (normalizedEndpointNormFactor_coeffCommute D Sc z.1 i z.2 x
      (h z (by simp))).mul (ih fun a ha => h a (by simp [ha]))

theorem eval₂_normalizedEndpointNormPolynomial (i : I) (xs : List (I × B)) (x : B)
    (h : ∀ z ∈ xs, ∀ n : ℕ, (n : ZMod 2) * D.parity z.1 = 0 → Commute (z.2 ^ n) x) :
    (normalizedEndpointNormPolynomial D Sc i xs).eval₂ (RingHom.id B) x =
      algebraMap k B (((xs.map fun z => (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
        (xs.map fun z => endpointNormFactor D Sc z.1 i z.2 x).prod := by
  induction xs with
  | nil => simp [normalizedEndpointNormPolynomial]
  | cons z zs ih =>
    have ht := fun a ha => h a (List.mem_cons_of_mem z ha)
    rw [normalizedEndpointNormPolynomial,
      (normalizedEndpointNormPolynomial_coeffCommute D Sc i zs x ht).eval_mul,
      eval₂_normalizedEndpointNormFactor D Sc z.1 i z.2 x
        (h z (by simp) 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]))
        (fun hp => by simpa using h z (by simp) 1 (by rw [parity_eq_zero_of_ne_one hp, mul_zero])),
      ih ht]
    simp only [List.map_cons, List.prod_cons, Units.val_mul, map_mul]
    rw [mul_assoc, ← mul_assoc (endpointNormFactor D Sc z.1 i z.2 x),
      ← Algebra.commutes, ← mul_assoc, ← mul_assoc]
    exact mul_assoc _ _ _

open CategoryTheory

def endpointOldDotEntries (w : List I) : ℕ → List I → List (I × End ((pres D Sc).obj (ob D w)))
  | _, [] => []
  | p, j :: ν => (j, dotE D Sc w p) :: endpointOldDotEntries w (p + 1) ν

theorem endpointOldDotEntries_pow_commute (i : I) (ν l : List I) :
    ∀ z ∈ endpointOldDotEntries D Sc (l ++ ν ++ [i]) l.length ν,
      ∀ n : ℕ, (n : ZMod 2) * D.parity z.1 = 0 →
        Commute (z.2 ^ n) (dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length)) := by
  induction ν generalizing l with
  | nil => simp [endpointOldDotEntries]
  | cons j ν ih =>
    intro z hz n hn
    simp only [endpointOldDotEntries, List.mem_cons] at hz
    rcases hz with rfl | hz
    · have hh := norm_oldDot_pow_commute D Sc l ν j i n hn
      have hw : l ++ [j] ++ ν ++ [i] = l ++ (j :: ν) ++ [i] := by simp
      rw [hw] at hh
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ν.length] using hh
    · have hh := ih (l ++ [j])
      have hw : (l ++ [j]) ++ ν ++ [i] = l ++ (j :: ν) ++ [i] := by simp
      rw [hw] at hh
      simp only [List.length_append, List.length_singleton] at hh
      have hc := hh z hz n hn
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ν.length] using hc

theorem endpointOldDotEntries_eval_prod (i : I) (w : List I) (moving old : ℕ) (ν : List I) :
    ((endpointOldDotEntries D Sc w old ν).map fun z =>
      endpointNormFactor D Sc z.1 i z.2 (dotE D Sc w moving)).prod =
      endpointNormAux D Sc i w moving old ν := by
  induction ν generalizing old with
  | nil => rfl
  | cons j ν ih =>
    simp only [endpointOldDotEntries, List.map_cons, List.prod_cons, endpointNormAux, ih]

theorem eval₂_normalizedEndpointNormPolynomial_dotE (i : I) (l ν : List I) :
    let xs := endpointOldDotEntries D Sc (l ++ ν ++ [i]) l.length ν
    (normalizedEndpointNormPolynomial D Sc i xs).eval₂ (RingHom.id _)
        (dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length)) =
      algebraMap k _ (((xs.map fun z => (endpointNormLeadingUnit D Sc z.1 i)⁻¹).prod : kˣ) : k) *
        endpointNorm D Sc i l ν := by
  dsimp only
  rw [eval₂_normalizedEndpointNormPolynomial D Sc _ _ _
    (endpointOldDotEntries_pow_commute D Sc i ν l), endpointOldDotEntries_eval_prod]
  rfl

end OddMath.QuiverHecke
end

end

section

/-! # Full ELV polynomial at the append endpoint

`relation_comp_move` transports the finite all-colour cyclotomic polynomial
through G with its total coefficient parity sign. This provides the ordered
coefficient comparison in `DeformedBoundaryDivision.md` §3. It imposes no
cyclotomic relation on the moving endpoint.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def endpointCoefficient (i : I) (j : Fin (cutoff i + 1)) : SKM.SYM D k :=
  if h : D.parity i = 1 then
    SKM.SYM.elvMonicCoefficient D k ⟨i, h⟩ (cutoff i) j
  else SKM.SYM.evenMonicCoefficient D k i (cutoff i) j

private theorem endpointCoefficient_parity (i : I) (j : Fin (cutoff i + 1)) :
    SKM.SYM.polynomialExteriorEquiv D k (endpointCoefficient D cutoff i j) ∈
      SKM.SYM.polynomialExteriorParity D k
        (cutoff i • D.parity i - j.val • D.parity i) := by
  unfold endpointCoefficient
  split_ifs with hi
  · simpa only [hi, nsmul_eq_mul, mul_one] using
      (SKM.SYM.elvMonicCoefficient_mem_parity (k := k) D ⟨i, hi⟩ (cutoff i) j)
  · have he : D.parity i = 0 := (parity_eq_zero_or_one (D.parity i)).resolve_right hi
    simp only [he, nsmul_zero, sub_self, SKM.SYM.evenMonicCoefficient, map_smul]
    apply Submodule.smul_mem
    cases cutoff i - j.val with
    | zero =>
        simpa only [SKM.SYM.evenCyclotomicCoefficient, map_one] using
          (SetLike.GradedOne.one_mem : (1 : SKM.SYM.PolynomialExterior D k) ∈
            SKM.SYM.polynomialExteriorParity D k 0)
    | succ n => exact SKM.SYM.polynomialExterior_e_mem_even D k i n

private theorem relation_as_polynomial (i : I) (v : List I) :
    relation D Sc cutoff i v =
      (elvQuotientFunctor D Sc cutoff).map
        (coefficientDotPolynomial D Sc (i :: v) 0 (cutoff i)
          (endpointCoefficient D cutoff i)) := by
  unfold relation endpointCoefficient
  dsimp only [elvQuotientFunctor]
  split_ifs with hi
  · apply congrArg (elvQuotientMap D Sc cutoff _ _)
    exact (elvDotPolynomial_first D Sc ⟨i, hi⟩ v (cutoff i)).symm
  · apply congrArg (elvQuotientMap D Sc cutoff _ _)
    unfold evenCyclotomic deformedCyclotomic coefficientDotPolynomial
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [dotE_pow, firstDotPower, List.map_replicate]

/-- The full finite ELV polynomial at the last strand, with coefficients on the left. -/
def endpointELV (i : I) (v : List I) : hom D Sc cutoff (v ++ [i]) (v ++ [i]) :=
  ∑ j : Fin (cutoff i + 1), singleCoefficient D cutoff i j ⊗ₜ[k]
    (dotE D Sc (v ++ [i]) v.length ^ j.val : End _)

private theorem endpointELV_as_polynomial (i : I) (v : List I) :
    endpointELV D Sc cutoff i v =
      (elvQuotientFunctor D Sc cutoff).map
        (coefficientDotPolynomial D Sc (v ++ [i]) v.length (cutoff i)
          (endpointCoefficient D cutoff i)) := by
  change _ = elvQuotientMap D Sc cutoff _ _ _
  unfold endpointELV coefficientDotPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (elvQuotientMap_source D Sc cutoff (endpointCoefficient D cutoff i j)
    (dotE D Sc (v ++ [i]) v.length ^ j.val)).symm

private theorem move_as_map (i : I) (v : List I) :
    move D Sc cutoff i v =
      (elvQuotientFunctor D Sc cutoff).map
        (sourceCoefficientHom D Sc 1 (moveHom D Sc i [] v)) := by
  change _ = elvQuotientMap D Sc cutoff _ _ _
  rw [elvQuotientMap_source, map_one]
  rfl

/-- Full-coefficient moving-polynomial transport, at every colour and cutoff. -/
theorem relation_comp_move (i : I) (v : List I) :
    relation D Sc cutoff i v ≫ move D Sc cutoff i v =
      sign k ((cutoff i • D.parity i) * (D.parity i * wordSumParity D v)) •
        (move D Sc cutoff i v ≫ endpointELV D Sc cutoff i v) := by
  have h := coefficientDotPolynomial_comp_moveHom D Sc i [] v (cutoff i)
    (endpointCoefficient D cutoff i) (cutoff i • D.parity i)
    (endpointCoefficient_parity D cutoff i)
  have hq := congrArg (fun f => (elvQuotientFunctor D Sc cutoff).map f) h
  rw [relation_as_polynomial, endpointELV_as_polynomial, move_as_map]
  simp only [List.nil_append, List.length_nil, zero_add,
    Functor.map_comp, Functor.map_smul] at hq
  dsimp only [elvQuotientFunctor] at hq ⊢
  exact hq
end OddMath.QuiverHecke.ELV
end

end
