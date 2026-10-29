/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependDescent
import OddMath.QuiverHecke.CyclotomicAction.MoveHomSnoc
/-!
# Moving powers in full ELV old-Hom coordinates

The operator comparison in `DeformedGlobalQP.md` §1: precomposition by the
actual moving square shifts the prepend exponent by two, and at even colour
the moving dot shifts it by one. The old quotient Hom coefficients retain the
full exterior algebra. The proofs use super interchange and the proved
`prependOldCoordinateEquiv`, without flatness or moving cyclotomic relations.
The actual old source action preserves the moving-exponent filtration, and
finite support proves injectivity of the square and even-dot differences.
The positioned-dot comparison requires a nonempty old word, as in the
cancellation step of QP; no all-prefix QP identity is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace PrependIdx
variable {i : I} {v w : List I}
def shift (x : PrependIdx i v w) (d : ℕ) : PrependIdx i v w :=
  ⟨(d + x.1.1, x.1.2), x.2⟩
end PrependIdx
namespace ELVOld
private theorem dotPower_mem (i : I) (v : List I) (d : ℕ) :
    (dotE D Sc (i :: v) 0 ^ d : End _) ∈ parity (R := k) _ _ (d • D.parity i) := by
  have hx : dotE D Sc (i :: v) 0 ∈ parity (R := k) _ _ (D.parity i) :=
    positionedDot_parity D Sc [] v i
  induction d with
  | zero => simpa only [pow_zero, zero_nsmul, End.one_def] using id_mem (R := k) _
  | succ d ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm] using
      comp_mem hx ih
private theorem dotPower_whisker (i : I) (v : List I) (d : ℕ) :
    (dotE D Sc [i] 0 ^ d : End _) ▷ (pres D Sc).obj (ob D v) =
      dotE D Sc (i :: v) 0 ^ d := by
  change whiskerWordRingHom D Sc [i] v (_ ^ d) = _
  rw [map_pow, whiskerWordRingHom_apply, dotE_whiskerRight D Sc [i] v 0 (by simp)]
  rfl
private theorem dotPower_insert_affine (i : I) {v t : List I} (d : ℕ)
    (hd : d • D.parity i = 0)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t)) :
    (dotE D Sc (i :: v) 0 ^ d : End _) ≫ affineInsert D Sc i v t f =
      affineInsert D Sc i v t f ≫ (dotE D Sc (i :: t) 0 ^ d : End _) := by
  induction f using Supercategory.induction_on (R := k) (C := (pres D Sc).Presented) with
  | zero => simp only [map_zero, Limits.comp_zero, Limits.zero_comp]
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, Preadditive.add_comp, hf, hg]
  | hom q f hf =>
    rw [← dotPower_whisker D Sc i v d, ← dotPower_whisker D Sc i t d]
    exact MonoidalSupercategory.interchange_of_even_left
      (hd ▸ dotPower_mem D Sc i [] d) hf
def movingPower (i : I) (v : List I) (d : ℕ) : hom D Sc cutoff (i :: v) (i :: v) :=
  (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    (dotE D Sc (i :: v) 0 ^ d : End _)

theorem movingPower_insert (i : I) {v t : List I} (d : ℕ)
    (hd : d • D.parity i = 0) (r : hom D Sc cutoff v t) :
    movingPower D Sc cutoff i v d ≫ insert D Sc cutoff i v t r =
      insert D Sc cutoff i v t r ≫ movingPower D Sc cutoff i t d := by
  induction r using BoxProd.induction_on_homogeneous with
  | zero => simp only [map_zero, Limits.comp_zero, Limits.zero_comp]
  | add r s hr hs => simp only [map_add, Preadditive.comp_add, Preadditive.add_comp, hr, hs]
  | tmul p q a f ha hf =>
    change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff at a
    change ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t)) at f
    change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
      (Y := obj D Sc cutoff (i :: v)) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (i :: t)) a (affineInsert D Sc i v t f) =
      BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
        (Y := obj D Sc cutoff (i :: t)) a (affineInsert D Sc i v t f) ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (i :: t))
        (Y := obj D Sc cutoff (i :: t)) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _
    have hi : affineInsert D Sc i v t f ∈ parity (R := k) _ _ q :=
      MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D [i])) hf
    rw [BoxProd.tmulHom_comp_tmulHom
      (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: v))
      (Z := obj D Sc cutoff (i :: t)) (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
        SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem) _ a hi,
      BoxProd.tmulHom_comp_tmulHom
      (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: t))
      (Z := obj D Sc cutoff (i :: t)) ha _ (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
        (hd ▸ dotPower_mem D Sc i t d)]
    simp only [koszulSign_zero_left, koszulSign_zero_right, one_smul,
      dotPower_insert_affine D Sc i d hd f]
    change (a * 1) ⊗ₜ[k] _ = (1 * a) ⊗ₜ[k] _
    rw [mul_one, one_mul]

theorem prependTail_shift {i : I} {v w : List I} (x : PrependIdx i v w) (d : ℕ) :
    (dotE D Sc (i :: x.oldTarget) 0 ^ d : End _) ≫ prependTail D Sc x =
      prependTail D Sc (x.shift d) := by
  rw [dotE_pow, prependTail, cl_comp]
  apply cl_eq_cl
  simp only [PrependIdx.shift, List.replicate_add, List.map_append, List.append_assoc,
    List.map_replicate]

theorem movingPower_relations (i : I) {v w : List I} (d : ℕ)
    (hd : d • D.parity i = 0) {h : hom D Sc cutoff (i :: v) w}
    (hh : h ∈ relations D Sc cutoff i v w) :
    movingPower D Sc cutoff i v d ≫ h ∈ relations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, movingPower_insert D Sc cutoff i d hd, Category.assoc]
    exact Submodule.subset_span ⟨t, r, hr, _, rfl⟩
  | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

/-- Right multiplication in algebra order, hence precomposition in diagram order. -/
def movingPowerTarget (i : I) (v w : List I) (d : ℕ) (hd : d • D.parity i = 0) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (relations D Sc cutoff i v w)
    (Linear.leftComp k _ (movingPower D Sc cutoff i v d))
    (fun _ hh => movingPower_relations D Sc cutoff i d hd hh)

@[simp] theorem movingPowerTarget_projection (i : I) (v w : List I) (d : ℕ)
    (hd : d • D.parity i = 0) (h : hom D Sc cutoff (i :: v) w) :
    movingPowerTarget D Sc cutoff i v w d hd (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w (movingPower D Sc cutoff i v d ≫ h) := rfl

private theorem movingPower_tail {i : I} {v w : List I} (x : PrependIdx i v w) (d : ℕ) :
    movingPower D Sc cutoff i x.oldTarget d ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x :
        hom D Sc cutoff (i :: x.oldTarget) w) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc (x.shift d) : hom D Sc cutoff (i :: x.oldTarget) w) := by
  change BoxProd.tmulHom (X := obj D Sc cutoff (i :: x.oldTarget))
    (Y := obj D Sc cutoff (i :: x.oldTarget)) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (i :: x.oldTarget))
        (Y := obj D Sc cutoff w) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ = _
  rw [BoxProd.tmulHom_comp_tmulHom
    (X := obj D Sc cutoff (i :: x.oldTarget)) (Y := obj D Sc cutoff (i :: x.oldTarget))
    (Z := obj D Sc cutoff w) (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
      SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem) _ (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (prependTail_mem D Sc x)]
  simp only [koszulSign_zero_left, one_smul, prependTail_shift]
  change (1 * 1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] _ = _
  rw [one_mul]

/-- The moving dot power shifts the exponent, with every old quotient coefficient retained. -/
theorem movingPower_pair_shift (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (hd : d • D.parity i = 0)
    (b : Old D Sc cutoff v x.oldTarget) :
    movingPowerTarget D Sc cutoff i v w d hd
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc (x.shift d)) b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  change movingPowerTarget D Sc cutoff i v w d hd
    (projection D Sc cutoff i v w (insert D Sc cutoff i v x.oldTarget (twist k p r) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x)) =
    projection D Sc cutoff i v w (insert D Sc cutoff i v x.oldTarget (twist k p r) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc (x.shift d))
  rw [movingPowerTarget_projection, ← Category.assoc,
    movingPower_insert D Sc cutoff i d hd, Category.assoc, movingPower_tail]

/-- Read back the old coefficient of a normalized single tail. -/
theorem prependOldCoordinate_pair (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (b : Old D Sc cutoff v x.oldTarget) :
    prependOldCoordinate D Sc cutoff p x
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) = b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  rw [pair_mk, prependOldCoordinate_projection, prependExtractOldQuotient_insert_tail, twist_twist]

/-- Different moving tails have disjoint old quotient coordinates. -/
theorem prependOldCoordinate_pair_off (p : ZMod 2) {i : I} {v w : List I}
    (x z : PrependIdx i v w) (h : x.tailKey ≠ z.tailKey)
    (b : Old D Sc cutoff v z.oldTarget) :
    prependOldCoordinate D Sc cutoff p x
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc z) b) = 0 := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v z.oldTarget).mkQ_surjective b
  rw [pair_mk, prependOldCoordinate_projection]
  exact prependExtractOldQuotient_insert_off_tail D Sc cutoff p x z h _

/-- Simultaneous coordinates detect the shifted coefficient for every finite coordinate vector. -/
theorem movingPower_coordinate_shift (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (d : ℕ) (hd : d • D.parity i = 0)
    (f : PrependOldCoordinates D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (movingPowerTarget D Sc cutoff i v w d hd
        (prependOldReconstruct D Sc cutoff p i v w f)) = f q := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply]
  | of t b =>
    change prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (movingPowerTarget D Sc cutoff i v w d hd
        (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t b))) = _
    rw [prependOldReconstruct, DirectSum.toModule_lof, movingPower_pair_shift]
    by_cases ht : t = q
    · subst t
      rw [prependOldCoordinate_pair, DirectSum.of_eq_same]
    · rw [prependOldCoordinate_pair_off]
      · symm
        exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht)
      · intro he
        apply ht
        apply Subtype.ext
        have hk : q.representative.tailKey = t.representative.tailKey := by
          apply Prod.ext
          · have hn := congrArg Prod.fst he
            change d + q.representative.1.1 = d + t.representative.1.1 at hn
            exact Nat.add_left_cancel hn
          · have hs := congrArg Prod.snd he
            exact hs
        exact t.representative_tailKey.symm.trans (hk.symm.trans q.representative_tailKey)

/-- In the old-Hom coordinate equivalence, the moving square raises the exponent by two. -/
theorem movingSquare_coordinate_shift (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (z : Target D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (q.representative.shift 2)
      (movingPowerTarget D Sc cutoff i v w 2 ((by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i)) z) =
      prependOldCoordinateEquiv D Sc cutoff p i v w z q := by
  simpa only [prependOldReconstruct_coordinateEquiv] using
    movingPower_coordinate_shift D Sc cutoff p q 2
      ((by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i))
      (prependOldCoordinateEquiv D Sc cutoff p i v w z)

/-- At even colour the moving dot itself raises the exponent by one. -/
theorem movingEvenDot_coordinate_shift (p : ZMod 2) {i : I} (hi : D.parity i = 0)
    {v w : List I} (q : PrependIdx.Tail i v w) (z : Target D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (q.representative.shift 1)
      (movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]) z) =
      prependOldCoordinateEquiv D Sc cutoff p i v w z q := by
  simpa only [prependOldReconstruct_coordinateEquiv] using
    movingPower_coordinate_shift D Sc cutoff p q 1 (by simp [hi])
      (prependOldCoordinateEquiv D Sc cutoff p i v w z)

/-- Actual right action of an old source endomorphism on the old-only quotient. -/
def oldSourceTarget (i : I) (v w : List I) (c : hom D Sc cutoff v v) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (relations D Sc cutoff i v w)
    (Linear.leftComp k _ (insert D Sc cutoff i v v c)) (by
      intro h hh
      change insert D Sc cutoff i v v c ≫ h ∈ relations D Sc cutoff i v w
      induction hh using Submodule.span_induction with
      | mem h hh =>
        obtain ⟨t, r, hr, f, rfl⟩ := hh
        rw [← Category.assoc, ← insert_comp]
        exact Submodule.subset_span ⟨t, c ≫ r, comp_ideal D Sc cutoff c hr, f, rfl⟩
      | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
      | smul a b _ hb => rw [Linear.comp_smul]; exact Submodule.smul_mem _ a hb)

def oldPrecomp (v t : List I) (c : hom D Sc cutoff v v) :
    Old D Sc cutoff v t →ₗ[k] Old D Sc cutoff v t :=
  (ideal D Sc cutoff v t).mapQ (ideal D Sc cutoff v t)
    (Linear.leftComp k _ c) (fun _ hh => comp_ideal D Sc cutoff c hh)

/-- The other operator changes only the old coefficient; the total parity twist is retained. -/
theorem oldSourceTarget_pair (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (c : hom D Sc cutoff v v)
    (b : Old D Sc cutoff v x.oldTarget) :
    oldSourceTarget D Sc cutoff i v w c
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x)
        (oldPrecomp D Sc cutoff v x.oldTarget (twist k p c) b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  change projection D Sc cutoff i v w
    (insert D Sc cutoff i v v c ≫ (insert D Sc cutoff i v x.oldTarget (twist k p r) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x)) =
    projection D Sc cutoff i v w
    (insert D Sc cutoff i v x.oldTarget (twist k p (twist k p c ≫ r)) ≫
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x)
  rw [twist_comp, twist_twist, insert_comp, Category.assoc]

/-- A coordinate above the input moving-exponent bound stays zero under the actual old action. -/
theorem oldSourceTarget_above (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (c : hom D Sc cutoff v v)
    (f : PrependOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, q.1.1 < x.1.1) :
    prependOldCoordinate D Sc cutoff p x
      (oldSourceTarget D Sc cutoff i v w c (prependOldReconstruct D Sc cutoff p i v w f)) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) := by
    exact (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [prependOldReconstruct, DirectSum.toModule_lof, oldSourceTarget_pair]
  apply prependOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst (he.trans q.representative_tailKey)
  have hh := h q hq
  change x.1.1 = q.1.1 at hn
  omega

/-- Finite support cancels the actual positive moving power against any old source action. -/
theorem movingPower_eq_oldSource (p : ZMod 2) (i : I) (v w : List I)
    (d : ℕ) (hd : d • D.parity i = 0) (hpos : 0 < d)
    (c : hom D Sc cutoff v v) (z : Target D Sc cutoff i v w)
    (hz : movingPowerTarget D Sc cutoff i v w d hd z = oldSourceTarget D Sc cutoff i v w c z) :
    z = 0 := by
  let f := prependOldCoordinateEquiv D Sc cutoff p i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff p i v w).injective (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have he := movingPower_coordinate_shift D Sc cutoff p q d hd f
  rw [prependOldReconstruct_coordinateEquiv, hz] at he
  have hb : ∀ t ∈ f.support, t.1.1 < (q.representative.shift d).1.1 := by
    intro t ht
    have hm := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change t.1.1 < d + q.representative.1.1
    omega
  have ho := oldSourceTarget_above D Sc cutoff p (q.representative.shift d) c f hb
  rw [prependOldReconstruct_coordinateEquiv] at ho
  exact (DFinsupp.mem_support_iff.mp hq) (he.symm.trans ho)

/-- The actual moving-minus-old right operator is injective; no filtration assumption is supplied. -/
theorem movingPower_sub_oldSource_injective (p : ZMod 2) (i : I) (v w : List I)
    (d : ℕ) (hd : d • D.parity i = 0) (hpos : 0 < d) (c : hom D Sc cutoff v v) :
    Function.Injective (movingPowerTarget D Sc cutoff i v w d hd -
      oldSourceTarget D Sc cutoff i v w c) := by
  intro z y h
  apply sub_eq_zero.mp
  apply movingPower_eq_oldSource D Sc cutoff p i v w d hd hpos c (z - y)
  simp only [LinearMap.sub_apply] at h
  simp only [map_sub]
  exact sub_eq_sub_iff_sub_eq_sub.mp h

/-- A pure positioned dot power in the full coefficient category. -/
def sourceDotPower (v : List I) (a d : ℕ) : hom D Sc cutoff v v :=
  (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] (dotE D Sc v a ^ d : End _)

private theorem affineInsert_positionedDot (i : I) (v : List I) (a : ℕ) :
    affineInsert D Sc i v v (dotE D Sc v a) = dotE D Sc (i :: v) (a + 1) := by
  change (pres D Sc).obj (ob D [i]) ◁ dotE D Sc v a = _
  rw [dotE_eq, cl_whiskerLeft, dotE_eq]
  apply cl_eq_cl
  simp [Nat.add_comm]

private theorem affineInsert_positionedDot_pow (i : I) (v : List I) (a d : ℕ) :
    affineInsert D Sc i v v (dotE D Sc v a ^ d : End _) =
      dotE D Sc (i :: v) (a + 1) ^ d := by
  induction d with
  | zero =>
    exact MonoidalSupercategory.whiskerLeft_id (R := k)
      ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D v))
  | succ d ih =>
    simp only [pow_succ, End.mul_def]
    change (pres D Sc).obj (ob D [i]) ◁ (dotE D Sc v a ≫ dotE D Sc v a ^ d) = _
    rw [MonoidalSupercategory.whiskerLeft_comp (R := k)]
    change affineInsert D Sc i v v (dotE D Sc v a) ≫
      affineInsert D Sc i v v (dotE D Sc v a ^ d) = _
    rw [affineInsert_positionedDot, ih]

theorem insert_sourceDotPower (i : I) (v : List I) (a d : ℕ) :
    insert D Sc cutoff i v v (sourceDotPower D Sc cutoff v a d) =
      sourceDotPower D Sc cutoff (i :: v) (a + 1) d := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    affineInsert D Sc i v v (dotE D Sc v a ^ d) = _
  rw [affineInsert_positionedDot_pow]
  rfl

/-- On a nonempty old word, this is right multiplication by x_(n+1)^d - x_1^d. -/
def lastDotDifference (i : I) (v w : List I) (d : ℕ) (hd : d • D.parity i = 0) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v (v.length - 1) d) -
    movingPowerTarget D Sc cutoff i v w d hd

/-- Exact comparison with the specified source positioned-dot difference, before quotienting. -/
theorem lastDotDifference_projection (i : I) (v w : List I) (hv : 0 < v.length)
    (d : ℕ) (hd : d • D.parity i = 0) (h : hom D Sc cutoff (i :: v) w) :
    lastDotDifference D Sc cutoff i v w d hd (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w
        ((sourceDotPower D Sc cutoff (i :: v) v.length d -
          sourceDotPower D Sc cutoff (i :: v) 0 d) ≫ h) := by
  change projection D Sc cutoff i v w
    (insert D Sc cutoff i v v (sourceDotPower D Sc cutoff v (v.length - 1) d) ≫ h) -
    projection D Sc cutoff i v w (movingPower D Sc cutoff i v d ≫ h) = _
  rw [insert_sourceDotPower, Nat.sub_add_cancel hv, ← map_sub, ← Preadditive.sub_comp]
  rfl

/-- Cancellation for the source difference with positive moving exponent. -/
theorem lastDotDifference_injective (p : ZMod 2) (i : I) (v w : List I)
    (d : ℕ) (hd : d • D.parity i = 0) (hpos : 0 < d) :
    Function.Injective (lastDotDifference D Sc cutoff i v w d hd) := by
  intro z y h
  apply movingPower_sub_oldSource_injective D Sc cutoff p i v w d hd hpos
    (sourceDotPower D Sc cutoff v (v.length - 1) d)
  change oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v (v.length - 1) d) z -
    movingPowerTarget D Sc cutoff i v w d hd z =
    oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v (v.length - 1) d) y -
    movingPowerTarget D Sc cutoff i v w d hd y at h
  change movingPowerTarget D Sc cutoff i v w d hd z - _ =
    movingPowerTarget D Sc cutoff i v w d hd y - _
  simpa only [neg_sub] using congrArg Neg.neg h

/-- The actual square difference required by the odd-colour QP cancellation. -/
theorem lastDotSquareDifference_injective (p : ZMod 2) (i : I) (v w : List I) :
    Function.Injective (lastDotDifference D Sc cutoff i v w 2
      ((by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i))) :=
  lastDotDifference_injective D Sc cutoff p i v w 2 _ (by decide)

/-- The actual linear difference required by even-colour QP cancellation. -/
theorem lastDotEvenDifference_injective (p : ZMod 2) (i : I) (hi : D.parity i = 0)
    (v w : List I) :
    Function.Injective (lastDotDifference D Sc cutoff i v w 1 (by simp [hi])) :=
  lastDotDifference_injective D Sc cutoff p i v w 1 _ (by decide)

end ELVOld
end OddMath.QuiverHecke
