import OddMath.QuiverHecke.CyclotomicAction.PrependCoordinates
import OddMath.QuiverHecke.CyclotomicAction.LastStrand
import OddMath.QuiverHecke.CyclotomicAction.PrefixScalarRelations
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend

/-!
# Moving shift relations

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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

end ELVOld
end OddMath.QuiverHecke
end

end

section

/-!
# All-prefix relation killing over the ELV coefficient category

The relation-killing identity (K) of `DeformedGlobalQP.md` §2, needed by the
repeated-colour QP induction. Naturality acts on the full coefficient-plus-diagram
parity. The old two-sided ideal, rather than a moving-strand cyclotomic quotient,
is used for vanishing. All cutoffs and both moving-colour parities are retained.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The affine moving chain with unit full ELV coefficient. -/
def move (i : I) (v : List I) : hom D Sc cutoff (i :: v) (v ++ [i]) :=
  (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] moveHom D Sc i [] v

private theorem move_induction_hom {v w : List I} {P : hom D Sc cutoff v w → Prop}
    (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

/-- Naturality of the moving chain for arbitrary full-coefficient old morphisms.
The word-parity equality is automatic on the permutation blocks used below. -/
theorem insert_comp_move (i : I) {v w : List I}
    (hp : wordSumParity D w = wordSumParity D v) (f : hom D Sc cutoff v w) :
    insert D Sc cutoff i v w f ≫ move D Sc cutoff i w =
      move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v w
        (twist k (D.parity i * wordSumParity D v) f) := by
  induction f using move_induction_hom D Sc cutoff with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | tmul q r a f ha hf =>
    change f ∈ parity (R := k) ((pres D Sc).obj (ob D v))
      ((pres D Sc).obj (ob D w)) r at hf
    have hm := moveHom_parity D Sc i [] w
    rw [hp] at hm
    have hnat := hom_comp_moveHom D Sc i f
    rw [twist_of_mem _ hf, MonoidalSupercategory.smul_whiskerRight (R := k),
      Linear.comp_smul] at hnat
    have ht : (a ⊗ₜ[k] f : hom D Sc cutoff v w) ∈
        parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) (q + r) :=
      BoxProd.tmul_mem_parity (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w) ha hf
    change insert D Sc cutoff i v w (a ⊗ₜ[k] f) ≫ move D Sc cutoff i w =
      move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v w
        (twist k (D.parity i * wordSumParity D v) (a ⊗ₜ[k] f))
    rw [twist_of_mem _ ht, map_smul, Linear.comp_smul]
    change (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
        (Y := obj D Sc cutoff (i :: w)) a (affineInsert D Sc i v w f)) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: w))
          (Y := obj D Sc cutoff (w ++ [i])) (SuperalgebraCat.ofElem 1)
          (moveHom D Sc i [] w) =
      sign k ((D.parity i * wordSumParity D v) * (q + r)) •
        (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (v ++ [i])) (SuperalgebraCat.ofElem 1)
          (moveHom D Sc i [] v) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (v ++ [i]))
          (Y := obj D Sc cutoff (w ++ [i])) a (affineRightContext D Sc [i] v w f))
    let a' : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff := a
    have hone : SuperalgebraCat.ofElem
        (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
        parity (R := k) (obj D Sc cutoff (i :: v)).fst
          (obj D Sc cutoff (v ++ [i])).fst 0 := id_mem (R := k) _
    have hr : affineRightContext D Sc [i] v w f ∈
        parity (R := k) (obj D Sc cutoff (v ++ [i])).snd
          (obj D Sc cutoff (w ++ [i])).snd r :=
      MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D [i])) hf
    rw [BoxProd.tmulHom_comp_tmulHom
      (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: w))
      (Z := obj D Sc cutoff (w ++ [i])) ha _ _ hm]
    change koszulSign q (D.parity i * wordSumParity D v) •
      ((1 * a') ⊗ₜ[k] (affineInsert D Sc i v w f ≫ moveHom D Sc i [] w)) =
      sign k ((D.parity i * wordSumParity D v) * (q + r)) •
        (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (v ++ [i])) (SuperalgebraCat.ofElem 1)
          (moveHom D Sc i [] v) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (v ++ [i]))
          (Y := obj D Sc cutoff (w ++ [i])) a (affineRightContext D Sc [i] v w f))
    rw [BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (v ++ [i]))
        (Z := obj D Sc cutoff (w ++ [i])) hone _ _ hr]
    change koszulSign q (D.parity i * wordSumParity D v) •
      ((1 * a') ⊗ₜ[k] (affineInsert D Sc i v w f ≫ moveHom D Sc i [] w)) =
      sign k ((D.parity i * wordSumParity D v) * (q + r)) •
        (koszulSign 0 r • ((a' * 1) ⊗ₜ[k]
          (moveHom D Sc i [] v ≫ affineRightContext D Sc [i] v w f)))
    rw [one_mul, mul_one, show affineInsert D Sc i v w f ≫ moveHom D Sc i [] w =
      sign k ((D.parity i * wordSumParity D v) * r) •
        (moveHom D Sc i [] v ≫ affineRightContext D Sc [i] v w f) from hnat]
    simp only [TensorProduct.tmul_smul, koszulSign_smul (R := k), zero_mul,
      sign_zero, one_smul, smul_smul, ← sign_add, mul_add, mul_comm q]

/-- Any old ideal morphism kills after the moving chain, in every right context.
No homogeneity of the old morphism or ambient continuation is required. -/
theorem projection_move_ideal_context (i : I) {v w : List I}
    (hp : wordSumParity D w = wordSumParity D v) (σ z : List I)
    (f : hom D Sc cutoff v w) (hf : f ∈ ideal D Sc cutoff v w)
    (h : hom D Sc cutoff ((w ++ [i]) ++ σ) z) :
    projection D Sc cutoff i (v ++ σ) z
      (rightContext D Sc cutoff σ (i :: v) (w ++ [i])
        (move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v w f) ≫ h) = 0 := by
  have hn := insert_comp_move D Sc cutoff i hp
    (twist k (D.parity i * wordSumParity D v) f)
  rw [twist_twist] at hn
  rw [← hn, rightContext_comp, rightContext_insert, Category.assoc]
  exact projection_old_ideal D Sc cutoff i
    (ideal_rightContext D Sc cutoff σ (twist_ideal D Sc cutoff _ hf)) _

/-- Full-coefficient prefix killing with an arbitrary old Hom before the relation,
and an arbitrary spectator context and ambient continuation. -/
theorem projection_prefix_relation_context (i j : I) {v t : List I}
    (hp : wordSumParity D (j :: t) = wordSumParity D v) (σ z : List I)
    (f : hom D Sc cutoff v (j :: t))
    (h : hom D Sc cutoff (((j :: t) ++ [i]) ++ σ) z) :
    projection D Sc cutoff i (v ++ σ) z
      (rightContext D Sc cutoff σ (i :: v) ((j :: t) ++ [i])
        (move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v (j :: t) f) ≫
        relation D Sc cutoff j ((t ++ [i]) ++ σ) ≫ h) = 0 := by
  have hz := projection_move_ideal_context D Sc cutoff i hp σ z
    (f ≫ relation D Sc cutoff j t)
    (comp_ideal D Sc cutoff f (relation_mem D Sc cutoff j t)) h
  rw [rightContext_comp D Sc cutoff [i] f (relation D Sc cutoff j t),
    rightContext_relation D Sc cutoff [i] j t] at hz
  rw [← Category.assoc, rightContext_comp] at hz
  have hr := rightContext_relation D Sc cutoff σ j (t ++ [i])
  change rightContext D Sc cutoff σ ((j :: t) ++ [i]) ((j :: t) ++ [i])
    (relation D Sc cutoff j (t ++ [i])) = relation D Sc cutoff j ((t ++ [i]) ++ σ) at hr
  rw [hr, Category.assoc] at hz
  exact hz

/-- The all-prefix identity (K), including arbitrary right contexts. The bare
crossing prefix is the existing `lastToFirstHom`. The target retains arbitrary
full ELV old morphisms, and the polynomial includes coefficient parity. -/
theorem allPrefix_relation_context (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff (((i :: μ) ++ [i]) ++ σ) z) :
    projection D Sc cutoff i ((μ ++ [i]) ++ σ) z
      (rightContext D Sc cutoff σ (i :: (μ ++ [i])) ((i :: μ) ++ [i])
        (move D Sc cutoff i (μ ++ [i]) ≫
          rightContext D Sc cutoff [i] (μ ++ [i]) (i :: μ)
            ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
              lastToFirstHom D Sc i μ)) ≫
        relation D Sc cutoff i ((μ ++ [i]) ++ σ) ≫ h) = 0 := by
  apply projection_prefix_relation_context
  simp only [wordSumParity, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact add_comm _ _

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Repeated-colour QP cancellation over ELV coefficients

The repeated-even step of `DeformedGlobalQP.md` §3 in the old-only quotient.
The library's even crossing convention contributes a minus sign, as in
`PrefixQPEquation.lean`; no coefficient or cyclotomic polynomial is cancelled.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Include an affine Hom with unit coefficient. -/
def affineUnit (v w : List I) :
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) →ₗ[k] hom D Sc cutoff v w :=
  TensorProduct.mk k (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ 1

theorem affineUnit_comp {v w z : List I}
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w))
    (g : (pres D Sc).obj (ob D w) ⟶ (pres D Sc).obj (ob D z)) :
    affineUnit D Sc cutoff v z (f ≫ g) =
      affineUnit D Sc cutoff v w f ≫ affineUnit D Sc cutoff w z g := by
  induction g using Supercategory.induction_on (R := k) (C := (pres D Sc).Presented) with
  | zero => simp only [Limits.comp_zero, map_zero]
  | add g h hg hh => simp only [Preadditive.comp_add, map_add, hg, hh]
  | hom q g hg =>
    symm
    change BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w)
      (SuperalgebraCat.ofElem 1) f ≫
        BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff z)
          (SuperalgebraCat.ofElem 1) g = _
    rw [BoxProd.tmulHom_comp_tmulHom
      (show (SuperalgebraCat.ofElem (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ∈
        parity (R := k) (obj D Sc cutoff v).fst (obj D Sc cutoff w).fst 0 from
        id_mem (R := k) _) f (SuperalgebraCat.ofElem 1) hg]
    simp only [koszulSign_zero_left, one_smul]
    change (1 * 1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] _ = _
    rw [one_mul]
    rfl

/-- Cancellation at any old position; the moving strand is never specialized. -/
theorem projection_even_difference_cancel (i : I) (hi : D.parity i = 0)
    (v z : List I) (a : ℕ) (h : hom D Sc cutoff (i :: v) z)
    (hh : projection D Sc cutoff i v z
      ((sourceDotPower D Sc cutoff (i :: v) (a + 1) 1 -
        sourceDotPower D Sc cutoff (i :: v) 0 1) ≫ h) = 0) :
    projection D Sc cutoff i v z h = 0 := by
  apply movingPower_eq_oldSource D Sc cutoff 0 i v z 1 (by simp [hi]) (by decide)
    (sourceDotPower D Sc cutoff v a 1)
  change projection D Sc cutoff i v z (movingPower D Sc cutoff i v 1 ≫ h) =
    projection D Sc cutoff i v z (insert D Sc cutoff i v v
      (sourceDotPower D Sc cutoff v a 1) ≫ h)
  rw [insert_sourceDotPower]
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hh
  exact hh.symm

/-- QP evaluated after the full first-position relation and an arbitrary continuation. -/
def qpEval (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: μ) ++ σ) z) :
    End ((pres D Sc).obj (ob D (i :: μ))) →ₗ[k] Target D Sc cutoff i (μ ++ σ) z :=
  (projection D Sc cutoff i (μ ++ σ) z).comp
    ((Linear.rightComp k _ (relation D Sc cutoff i (μ ++ σ) ≫ h)).comp
      ((rightContext D Sc cutoff σ (i :: μ) (i :: μ)).comp
        (affineUnit D Sc cutoff (i :: μ) (i :: μ))))

theorem qpEval_even_difference_cancel (i : I) (hi : D.parity i = 0)
    (μ σ z : List I) (a : ℕ) (ha : a < μ.length)
    (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ))))
    (hf : qpEval D Sc cutoff i μ σ z h
      ((dotE D Sc (i :: μ) (a + 1) - dotE D Sc (i :: μ) 0) ≫ f) = 0) :
    qpEval D Sc cutoff i μ σ z h f = 0 := by
  apply projection_even_difference_cancel D Sc cutoff i hi (μ ++ σ) z a
  change projection D Sc cutoff i (μ ++ σ) z
    (rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ)
        ((dotE D Sc (i :: μ) (a + 1) - dotE D Sc (i :: μ) 0) ≫ f)) ≫
      (relation D Sc cutoff i (μ ++ σ) ≫ h)) = 0 at hf
  rw [affineUnit_comp, rightContext_comp, Category.assoc] at hf
  have he : rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ)
        (dotE D Sc (i :: μ) (a + 1) - dotE D Sc (i :: μ) 0)) =
      sourceDotPower D Sc cutoff (i :: (μ ++ σ)) (a + 1) 1 -
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) 0 1 := by
    rw [map_sub, map_sub]
    have ht (b : ℕ) (hb : b < (i :: μ).length) :
        rightContext D Sc cutoff σ (i :: μ) (i :: μ)
          (affineUnit D Sc cutoff (i :: μ) (i :: μ) (dotE D Sc (i :: μ) b)) =
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) b 1 := by
      change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        (dotE D Sc (i :: μ) b ▷ (pres D Sc).obj (ob D σ)) =
        (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          (dotE D Sc (i :: (μ ++ σ)) b ^ 1)
      rw [pow_one, dotE_whiskerRight D Sc (i :: μ) σ b hb]
      rfl
    rw [ht (a + 1) (by simp; omega), ht 0 (by simp)]
  rw [he] at hf
  exact hf

/-- The repeated-even recursion in every right context, with its surviving minus sign.
All exterior coefficients remain in the relation and in the arbitrary continuation. -/
theorem qp_repeated_even (i : I) (hi : D.parity i = 0) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: (μ ++ [i])) ++ σ) z) :
    qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫ lastToFirstHom D Sc i (μ ++ [i])) =
    -qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveWhisker D Sc i μ ≫
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) := by
  let E := dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) -
    dotE D Sc (i :: (μ ++ [i])) 0
  let A : (pres D Sc).obj (ob D (i :: (μ ++ [i]))) ⟶
      (pres D Sc).obj (ob D (i :: (μ ++ [i]))) := moveWhisker D Sc i μ ≫
    (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))
  let B := moveWhisker D Sc i μ ≫ lastToFirstHom D Sc i (μ ++ [i])
  have hK := allPrefix_relation_context D Sc cutoff i μ σ z h
  change projection D Sc cutoff i ((μ ++ [i]) ++ σ) z
    (rightContext D Sc cutoff σ _ _
      (affineUnit D Sc cutoff _ _ (moveHom D Sc i [] (μ ++ [i])) ≫
        affineUnit D Sc cutoff _ _
          (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) ≫
      relation D Sc cutoff i ((μ ++ [i]) ++ σ) ≫ h) = 0 at hK
  rw [← affineUnit_comp] at hK
  have hzero : qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (E ≫ (A + E ≫ B)) = 0 := by
    change qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) = 0 at hK
    rw [moveHom_append_self, moveWhisker_comp_sameIntertwiner_even D Sc i hi μ] at hK
    simpa only [E, A, B, lastToFirstHom_append_self, Preadditive.add_comp,
      Preadditive.comp_add, Category.assoc] using hK
  have hc := qpEval_even_difference_cancel D Sc cutoff i hi (μ ++ [i]) σ z μ.length
    (by simp) h (A + E ≫ B) hzero
  rw [map_add] at hc
  rw [moveHom_lastToFirstHom_append_self_even D Sc i hi μ]
  exact eq_neg_of_add_eq_zero_right hc

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Coefficient balance for the ELV old-generator P map

The coefficient-only balance needed in `DeformedGlobalQP.md` §4. For the
old-generator morphism `W = affineUnit(lastToFirstHom) ≫ relation`, the total
parity is the sum of the crossing-word parity and the full relation parity.
The theorem `oldGenerator_scalar_balance` moves an arbitrary ELV coefficient
through `W`, with this total-parity twist and the right-context inclusion.

Supercommutativity is proved, not assumed: exterior-generator anticommutation
extends to the parity pieces, then to the polynomial/exterior model and its
homogeneous ELV quotient. The signed box product supplies the remaining affine
Koszul sign. No old cyclotomic relation is killed in this calculation, and no
homogeneity assumption is imposed on the coefficient in the final theorem.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVPScalar
universe u
variable {k M : Type u} [CommRing k] [AddCommGroup M] [Module k M]

private theorem exterior_ι_pow {n : ℕ} {b : ExteriorAlgebra k M}
    (hb : b ∈ (ExteriorAlgebra.ι k : M →ₗ[k] ExteriorAlgebra k M).range ^ n) (m : M) :
    ExteriorAlgebra.ι k m * b = koszulSign 1 (n : ZMod 2) • (b * ExteriorAlgebra.ι k m) := by
  induction hb using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y n hx hy ihx ihy => simp only [mul_add, add_mul, ihx, ihy, smul_add]
  | mem_mul a ha n x hx ih =>
    obtain ⟨a, rfl⟩ := ha
    have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := k) m a)
    rw [← mul_assoc, h, neg_mul, mul_assoc, ih, mul_smul_comm, ← mul_assoc]
    simp only [Nat.cast_succ, koszulSign_add_right, koszulSign_one_one,
      mul_neg, neg_smul, mul_one]

private theorem exterior_pow_comm {n l : ℕ} {a b : ExteriorAlgebra k M}
    (ha : a ∈ (ExteriorAlgebra.ι k : M →ₗ[k] ExteriorAlgebra k M).range ^ n)
    (hb : b ∈ (ExteriorAlgebra.ι k : M →ₗ[k] ExteriorAlgebra k M).range ^ l) :
    a * b = koszulSign (n : ZMod 2) (l : ZMod 2) • (b * a) := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y n hx hy ihx ihy => simp only [mul_add, add_mul, ihx, ihy, smul_add]
  | mem_mul a ha n x hx ih =>
    obtain ⟨a, rfl⟩ := ha
    rw [mul_assoc, ih, mul_smul_comm, ← mul_assoc, exterior_ι_pow hb,
      smul_mul_assoc, mul_assoc, smul_smul]
    simp only [Nat.cast_succ, koszulSign_add_left]

/-- Exterior parity pieces supercommute over any commutative ground ring. -/
theorem exterior_comm {p q : ZMod 2} {a b : ExteriorAlgebra k M}
    (ha : a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm k M) p)
    (hb : b ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm k M) q) :
    a * b = koszulSign p q • (b * a) := by
  induction ha using Submodule.iSup_induction' with
  | zero => simp
  | add x y hx hy ihx ihy => simp only [add_mul, mul_add, ihx, ihy, smul_add]
  | mem n a ha =>
    induction hb using Submodule.iSup_induction' with
    | zero => simp
    | add x y hx hy ihx ihy => simp only [add_mul, mul_add, ihx, ihy, smul_add]
    | mem m b hb =>
      obtain ⟨n, rfl⟩ := n
      obtain ⟨m, rfl⟩ := m
      exact exterior_pow_comm ha hb
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)

/-- The polynomial factor is even, so exterior supercommutativity extends by base change. -/
theorem polynomialExterior_comm {p q : ZMod 2} {a b : SKM.SYM.PolynomialExterior D k}
    (ha : a ∈ SKM.SYM.polynomialExteriorParity D k p)
    (hb : b ∈ SKM.SYM.polynomialExteriorParity D k q) :
    a * b = koszulSign p q • (b * a) := by
  change a ∈ (SKM.SYM.exteriorParity D k p).baseChange (MvPolynomial (I × ℕ) k) at ha
  change b ∈ (SKM.SYM.exteriorParity D k q).baseChange (MvPolynomial (I × ℕ) k) at hb
  rw [Submodule.baseChange_eq_span] at ha hb
  induction ha using Submodule.span_induction with
  | zero => simp
  | add x y hx hy ihx ihy => simp only [add_mul, mul_add, ihx, ihy, smul_add]
  | smul c x hx ih => simp only [smul_mul_assoc, mul_smul_comm, ih, smul_comm c]
  | mem a ha =>
    obtain ⟨a, ha, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | zero => simp
    | add x y hx hy ihx ihy => simp only [add_mul, mul_add, ihx, ihy, smul_add]
    | smul c x hx ih => simp only [smul_mul_assoc, mul_smul_comm, ih, smul_comm c]
    | mem b hb =>
      obtain ⟨b, hb, rfl⟩ := hb
      change (1 ⊗ₜ[k] a : SKM.SYM.PolynomialExterior D k) * (1 ⊗ₜ[k] b) =
        koszulSign p q • ((1 ⊗ₜ[k] b) * (1 ⊗ₜ[k] a))
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [exterior_comm ha hb, TensorProduct.tmul_smul]
/-- The coefficient quotient commutes with homogeneous projection. -/
theorem elvModelQuotient_proj (cutoff : I → ℕ) (p : ZMod 2)
    (a : SKM.SYM.PolynomialExterior D k) :
    SKM.SYM.elvModelQuotient (k := k) D cutoff (GradedAlgebra.proj (SKM.SYM.polynomialExteriorParity D k) p a) =
      GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p
        (SKM.SYM.elvModelQuotient (k := k) D cutoff a) := by
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.polynomialExteriorParity D k)
    (by simp) ?_ ?_ a
  · intro q a
    by_cases h : q = p
    · subst q
      simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ a.property,
        DirectSum.decompose_of_mem_same _ (SKM.SYM.elvModelQuotient_mem D a.property)]
    · simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne _ a.property h,
        DirectSum.decompose_of_mem_ne _ (SKM.SYM.elvModelQuotient_mem D a.property) h, map_zero]
  · intro a b ha hb
    simp only [map_add, ha, hb]

/-- Every homogeneous ELV coefficient has a homogeneous polynomial/exterior lift. -/
theorem elv_homogeneous_lift (cutoff : I → ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    ∃ b ∈ SKM.SYM.polynomialExteriorParity D k p, SKM.SYM.elvModelQuotient (k := k) D cutoff b = a := by
  obtain ⟨a, rfl⟩ := ((RingCon.mkₐ_surjective (α := k)
    (SKM.SYM.elvCoefficientIdeal D k cutoff).ringCon).comp
    (SKM.SYM.polynomialExteriorEquiv D k).symm.surjective) a
  refine ⟨GradedAlgebra.proj (SKM.SYM.polynomialExteriorParity D k) p a,
    (DirectSum.decompose (SKM.SYM.polynomialExteriorParity D k) a p).property, ?_⟩
  change SKM.SYM.elvModelQuotient (k := k) D cutoff a ∈
    SKM.SYM.elvCoefficientParity D cutoff p at ha
  change SKM.SYM.elvModelQuotient (k := k) D cutoff _ =
    SKM.SYM.elvModelQuotient (k := k) D cutoff a
  rw [elvModelQuotient_proj, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ ha]

/-- Graded commutativity of the full ELV coefficient algebra. -/
theorem elv_comm (cutoff : I → ℕ) {p q : ZMod 2}
    {a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p)
    (hb : b ∈ SKM.SYM.elvCoefficientParity D cutoff q) :
    a * b = koszulSign p q • (b * a) := by
  obtain ⟨a, ha', rfl⟩ := elv_homogeneous_lift D cutoff ha
  obtain ⟨b, hb', rfl⟩ := elv_homogeneous_lift D cutoff hb
  simpa only [map_mul, map_zsmul] using
    congrArg (SKM.SYM.elvModelQuotient (k := k) D cutoff) (polynomialExterior_comm D ha' hb')
variable (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
open ELVOld

def scalar (v : List I) : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
    hom D Sc cutoff v v :=
  (TensorProduct.mk k _ _).flip (𝟙 ((pres D Sc).obj (ob D v)))

theorem scalar_mem (v : List I) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    scalar D Sc cutoff v a ∈ parity (R := k) _ _ p := by
  have h := BoxProd.tmul_mem_parity
    (X := obj D Sc cutoff v) (Y := obj D Sc cutoff v) ha
    (id_mem (R := k) ((pres D Sc).obj (ob D v)))
  change scalar D Sc cutoff v a ∈ parity (R := k) _ _ (p + 0) at h
  simpa only [add_zero] using h

private theorem scalar_induction_hom {v w : List I} {P : hom D Sc cutoff v w → Prop}
    (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (obj D Sc cutoff v).snd ⟶ (obj D Sc cutoff w).snd),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

theorem scalar_slide_homogeneous {v w : List I} {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) (f : hom D Sc cutoff v w) :
    f ≫ scalar D Sc cutoff w a = scalar D Sc cutoff v a ≫ twist k p f := by
  induction f using scalar_induction_hom D Sc cutoff with
  | zero => simp only [Limits.zero_comp, map_zero, Limits.comp_zero]
  | add f g hf hg => simp only [Preadditive.add_comp, map_add, Preadditive.comp_add, hf, hg]
  | tmul r s b f hb hf =>
    have ht := BoxProd.tmul_mem_parity (X := obj D Sc cutoff v)
      (Y := obj D Sc cutoff w) hb hf
    change BoxProd.tmulHom b f ∈ parity (R := k) _ _ (r + s) at ht
    rw [twist_of_mem p ht, ← koszulSign_smul, Preadditive.comp_zsmul]
    change BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w) b f ≫
      BoxProd.tmulHom (X := obj D Sc cutoff w) (Y := obj D Sc cutoff w) a (𝟙 _) =
      koszulSign p (r + s) •
        (BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff v) a (𝟙 _) ≫
          BoxProd.tmulHom (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w) b f)
    rw [BoxProd.tmulHom_comp_tmulHom hb f a (id_mem (R := k) _),
      BoxProd.tmulHom_comp_tmulHom ha (𝟙 _) b hf]
    simp only [koszulSign_zero_right, one_smul, Category.comp_id, Category.id_comp]
    change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff at b
    change b ∈ SKM.SYM.elvCoefficientParity D cutoff r at hb
    change (a * b) ⊗ₜ[k] f = koszulSign p (r + s) • (koszulSign p s • ((b * a) ⊗ₜ[k] f))
    rw [elv_comm D cutoff ha hb, smul_smul,
      koszulSign_add_right, mul_assoc, koszulSign_mul_self, mul_one]
    exact map_zsmul ((TensorProduct.mk k _ _).flip f) _ _

theorem insert_scalar (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    insert D Sc cutoff i v v (scalar D Sc cutoff v a) = scalar D Sc cutoff (i :: v) a := by
  exact congrArg (fun f => a ⊗ₜ[k] f)
    (MonoidalSupercategory.whiskerLeft_id (R := k) ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D v)))

theorem rightContext_scalar (σ v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    rightContext D Sc cutoff σ v v (scalar D Sc cutoff v a) = scalar D Sc cutoff (v ++ σ) a := by
  exact congrArg (fun f => a ⊗ₜ[k] f)
    (MonoidalSupercategory.id_whiskerRight (R := k) ((pres D Sc).obj (ob D v)) ((pres D Sc).obj (ob D σ)))

theorem affineUnit_mem {v w : List I} {q : ZMod 2}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ parity (R := k) _ _ q) :
    affineUnit D Sc cutoff v w f ∈ parity (R := k) _ _ q := by
  have h := BoxProd.tmul_mem_parity (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w)
    (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
      parity (R := k) (obj D Sc cutoff v).fst (obj D Sc cutoff w).fst 0 from
      (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
        SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem)) hf
  change affineUnit D Sc cutoff v w f ∈ parity (R := k) _ _ (0 + q) at h
  simpa only [zero_add] using h

end OddMath.QuiverHecke.ELVPScalar
end

end

section

/-!
# The all-prefix QP identity

`DeformedGlobalQP.md`, §3 (the deformed form of Kang–Kashiwara–Oh, arXiv:1206.5933v2,
(8.14)–(8.17)): for every word `μ`, modulo endomorphisms of `i :: μ` that kill the
prescribed prepend target in every right context,

  `f_i(x₁) Tₙ Vₙ ≡ f_i(x₁) A_μ`,

where `A_μ` is the product over the positions `a` of `μ` of `Q_(i,μ_a)(x₁, x_(a+1))` when
`μ_a ≠ i`, of `(x_(a+1) − x₁)²` when `μ_a = i` is odd, and of `−1` when `μ_a = i` is even.

* `KillAll s Y`: `Y ⊗ 1_σ` kills on `i :: (s ++ σ)` for every right context `σ`;
* `goodAll`: the precompositions preserving `KillAll`, a subalgebra containing every
  `1_i ⊗ f` and the first dot;
* `KillAll.whiskerRight_cons`: adjoining a last spectator;
* `KillAll.of_sq_sub`, `KillAll.of_linear_even`: the two cancellations;
* `qpProduct`: the product `A_μ`;
* `killAll_qp`: the identity above.

The sign `−1` for an even repeated colour comes from the crossing convention of the
two-strand nilHecke relations used here (`EvenTwo`); with the opposite sign of the crossing
it disappears, as in the written argument.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Algebra

/-- Two elements commuting up to a scalar of square one: the square difference commutes with
the difference. -/
theorem squareDiff_mul_sub_comm {B : Type*} [Ring B] [Algebra k B] {x y : B} {c : k}
    (h : y * x = c • (x * y)) (hc : c * c = 1) :
    (y ^ 2 - x ^ 2) * (y - x) = (y - x) * (y ^ 2 - x ^ 2) := by
  have h1 : y ^ 2 * x = x * y ^ 2 := by
    rw [pow_two, mul_assoc, h, mul_smul_comm, ← mul_assoc, h, smul_mul_assoc, smul_smul, hc,
      one_smul, mul_assoc]
  have h2 : y * x ^ 2 = x ^ 2 * y := by
    rw [pow_two, ← mul_assoc, h, smul_mul_assoc, mul_assoc, h, mul_smul_comm, smul_smul, hc,
      one_smul, mul_assoc]
  rw [sub_mul, mul_sub, mul_sub, sub_mul, h1, ← h2]
  noncomm_ring

end Algebra

section Product

variable {D Sc}

theorem map_qPoly {A B : (pres D Sc).Presented} (φ : End A →ₐ[k] End B) (x y : End A)
    (j l : I) : φ (qPoly D Sc x y j l) = qPoly D Sc (φ x) (φ y) j l := by
  unfold qPoly
  split_ifs <;> simp only [map_sum, map_add, map_smul, map_mul, map_pow, map_one]

variable (D Sc) (i : I)

open Classical in
/-- The factor of `A_μ` at the position `b` of `μ`, whose letter is `x`:
`Q_(i,x)(x₁, x_(b+2))` for `x ≠ i`, `(x_(b+2) − x₁)²` for `x = i` odd and `−1` for `x = i`
even. -/
def qpFactor (μ : List I) (x : I) (b : ℕ) : End ((pres D Sc).obj (ob D (i :: μ))) :=
  if x = i then
    (if D.parity i = 1 then (dotE D Sc (i :: μ) (b + 1) - dotE D Sc (i :: μ) 0) ^ 2 else -1)
  else qPoly D Sc (dotE D Sc (i :: μ) 0) (dotE D Sc (i :: μ) (b + 1)) i x

/-- The product `A_μ` of the factors over the positions of `μ`. -/
def qpProduct (μ : List I) : End ((pres D Sc).obj (ob D (i :: μ))) :=
  ((List.range μ.length).map fun b => qpFactor D Sc i μ (μ.getD b i) b).prod

theorem qpFactor_whiskerRight (μ s : List I) (x : I) {b : ℕ} (hb : b < μ.length) :
    whiskerWordAlgHom D Sc (i :: μ) s (qpFactor D Sc i μ x b) =
      qpFactor D Sc i (μ ++ s) x b := by
  have h0 : whiskerWordAlgHom D Sc (i :: μ) s (dotE D Sc (i :: μ) 0) =
      dotE D Sc (i :: (μ ++ s)) 0 :=
    dotE_whiskerRight D Sc (i :: μ) s 0 (by simp)
  have h1 : whiskerWordAlgHom D Sc (i :: μ) s (dotE D Sc (i :: μ) (b + 1)) =
      dotE D Sc (i :: (μ ++ s)) (b + 1) :=
    dotE_whiskerRight D Sc (i :: μ) s (b + 1) (by simp; omega)
  unfold qpFactor
  split_ifs <;> simp only [map_pow, map_sub, map_neg, map_one, map_qPoly, h0, h1]

theorem qpProduct_append (μ : List I) (x : I) :
    qpProduct D Sc i (μ ++ [x]) =
      @id (End ((pres D Sc).obj (ob D (i :: (μ ++ [x])))))
          (whiskerWordAlgHom D Sc (i :: μ) [x] (qpProduct D Sc i μ)) *
        qpFactor D Sc i (μ ++ [x]) x μ.length := by
  unfold qpProduct
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.prod_append, map_list_prod, List.map_map]
  congr 1
  · congr 1
    refine List.map_congr_left fun b hb => ?_
    rw [List.mem_range] at hb
    simp only [Function.comp_apply]
    rw [qpFactor_whiskerRight D Sc i μ [x] _ hb, List.getD_append _ _ _ _ hb]
  · simp

theorem dotE_last_mul_first (μ : List I) :
    dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) * dotE D Sc (i :: (μ ++ [i])) 0 =
      SKM.zsign k (D.parity i * D.parity i) •
        (dotE D Sc (i :: (μ ++ [i])) 0 * dotE D Sc (i :: (μ ++ [i])) (μ.length + 1)) :=
  genE_interchange D Sc [] μ [] (.dot i) (.dot i) rfl rfl (by simp [Shape.dom]) rfl
    (by simp [Shape.dom])

end Product

variable [Fintype I] (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

section Context

/-- `Y` kills on `i :: (s ++ σ)` after right whiskering by every right context `σ`. -/
def KillAll (s : List I) (Y : End ((pres D Sc).obj (ob D (i :: s)))) : Prop :=
  ∀ (σ : List I) (h : (s ++ σ).length = n + 1),
    KillE D Sc i β a ha n ⟨s ++ σ, h⟩
      (Y ▷ (pres D Sc).obj (ob D σ) : End ((pres D Sc).obj (ob D (i :: (s ++ σ)))))

variable {D Sc i β a ha n} {s : List I}

/- The combinators below take morphisms `i :: s ⟶ i :: s`, so that sums and composites
are formed in the morphism groups. -/

theorem KillAll.add {Y Z : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) (hZ : KillAll D Sc i β a ha n s Z) :
    KillAll D Sc i β a ha n s (Y + Z) := fun σ h => by
  rw [MonoidalSupercategory.add_whiskerRight (R := k)]
  exact (hY σ h).add (hZ σ h)

theorem KillAll.neg {Y : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) : KillAll D Sc i β a ha n s (-Y) := fun σ h => by
  rw [MonoidalSupercategory.neg_whiskerRight (R := k)]
  exact (hY σ h).neg

theorem KillAll.sub {Y Z : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) (hZ : KillAll D Sc i β a ha n s Z) :
    KillAll D Sc i β a ha n s (Y - Z) := by
  rw [sub_eq_add_neg]
  exact hY.add hZ.neg

theorem KillAll.smul {Y : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) (c : k) :
    KillAll D Sc i β a ha n s (c • Y) := fun σ h => by
  rw [MonoidalSupercategory.smul_whiskerRight (R := k)]
  exact (hY σ h).smul c

theorem KillAll.zero : KillAll D Sc i β a ha n s (0 : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))) := fun σ h => by
  rw [MonoidalSupercategory.zero_whiskerRight (R := k)]
  exact killE_zero (w := ⟨s ++ σ, h⟩)

theorem KillAll.of_eq {Y Z : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D (i :: s))}
    (hY : KillAll D Sc i β a ha n s Y) (h : Y = Z) : KillAll D Sc i β a ha n s Z := h ▸ hY

end Context

section Equation

end Equation

end OddMath.QuiverHecke
end

end

section

/-!
# Repeated-odd QP recursion over ELV coefficients

The repeated-odd step of `DeformedGlobalQP.md` §3. The two prefix signs
cancel after square-difference cancellation and odd source-difference preservation
in the old-only quotient. No moving cyclotomic relation is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem dot_whisker (i : I) (v : List I) :
    dotE D Sc [i] 0 ▷ (pres D Sc).obj (ob D v) = dotE D Sc (i :: v) 0 := by
  rw [dotE_whiskerRight D Sc [i] v 0 (by simp)]
  rfl

private theorem odd_induction_hom {v w : List I} {P : hom D Sc cutoff v w → Prop}
    (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

private theorem movingPower_one (i : I) (v : List I) :
    movingPower D Sc cutoff i v 1 =
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] dotE D Sc (i :: v) 0 := by
  exact congrArg (fun f : End ((pres D Sc).obj (ob D (i :: v))) =>
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)
    (pow_one (dotE D Sc (i :: v) 0))

/-- The moving dot twists the total coefficient-plus-diagram parity of an old Hom. -/
theorem movingDot_insert (i : I) {v t : List I} (r : hom D Sc cutoff v t) :
    movingPower D Sc cutoff i v 1 ≫ insert D Sc cutoff i v t r =
      insert D Sc cutoff i v t (twist k (D.parity i) r) ≫
        movingPower D Sc cutoff i t 1 := by
  induction r using odd_induction_hom D Sc cutoff with
  | zero => simp only [map_zero, Limits.comp_zero, Limits.zero_comp]
  | add r s hr hs => simp only [map_add, Preadditive.comp_add, Preadditive.add_comp, hr, hs]
  | tmul p q a f ha hf =>
    change SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff at a
    have hx : dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) :=
      positionedDot_parity D Sc [] [] i
    have hxt : dotE D Sc (i :: t) 0 ∈ parity (R := k) _ _ (D.parity i) :=
      positionedDot_parity D Sc [] t i
    have ht : (a ⊗ₜ[k] f : hom D Sc cutoff v t) ∈
        parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff t) (p + q) :=
      BoxProd.tmul_mem_parity (X := obj D Sc cutoff v) (Y := obj D Sc cutoff t) ha hf
    change movingPower D Sc cutoff i v 1 ≫ insert D Sc cutoff i v t (a ⊗ₜ[k] f) =
      insert D Sc cutoff i v t (twist k (D.parity i) (a ⊗ₜ[k] f)) ≫ movingPower D Sc cutoff i t 1
    rw [twist_of_mem _ ht]
    change movingPower D Sc cutoff i v 1 ≫ insert D Sc cutoff i v t (a ⊗ₜ[k] f) =
      insert D Sc cutoff i v t (sign k (D.parity i * (p + q)) •
        (a ⊗ₜ[k] f : hom D Sc cutoff v t)) ≫ movingPower D Sc cutoff i t 1
    erw [map_smul]
    rw [Linear.smul_comp]
    rw [movingPower_one, movingPower_one]
    change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
        (Y := obj D Sc cutoff (i :: v)) (SuperalgebraCat.ofElem 1) (dotE D Sc (i :: v) 0) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (i :: t)) a (affineInsert D Sc i v t f) =
      sign k (D.parity i * (p + q)) •
        (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (i :: t)) a (affineInsert D Sc i v t f) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: t))
          (Y := obj D Sc cutoff (i :: t)) (SuperalgebraCat.ofElem 1) (dotE D Sc (i :: t) 0))
    erw [BoxProd.tmulHom_comp_tmulHom
      (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: v))
      (Z := obj D Sc cutoff (i :: t))
      (show (SuperalgebraCat.ofElem (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)) ∈
        parity (R := k) (obj D Sc cutoff (i :: v)).fst _ 0 from id_mem (R := k) _) _ _
      (MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D [i])) hf),
      BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: t))
        (Z := obj D Sc cutoff (i :: t)) ha _ _ hxt]
    have hn : dotE D Sc (i :: v) 0 ≫ affineInsert D Sc i v t f =
        koszulSign (D.parity i) q •
          (affineInsert D Sc i v t f ≫ dotE D Sc (i :: t) 0) := by
      rw [← dot_whisker D Sc i v, ← dot_whisker D Sc i t]
      exact MonoidalSupercategory.super_interchange hx hf
    change koszulSign 0 q • ((a * 1) ⊗ₜ[k]
      (dotE D Sc (i :: v) 0 ≫ affineInsert D Sc i v t f)) =
      sign k (D.parity i * (p + q)) • (koszulSign p (D.parity i) • ((1 * a) ⊗ₜ[k]
        (affineInsert D Sc i v t f ≫ dotE D Sc (i :: t) 0)))
    rw [hn]
    simp only [mul_one, one_mul, TensorProduct.tmul_smul, koszulSign_smul (R := k),
      zero_mul, sign_zero, smul_smul, ← sign_add, mul_add, mul_comm p, add_comm]
    rw [((by decide : ∀ a b : ZMod 2, a + (a + b) = b) _ _)]

/-- Precomposition by the moving odd dot preserves the defining old relations. -/
theorem movingDot_relations (i : I) {v w : List I} {h : hom D Sc cutoff (i :: v) w}
    (hh : h ∈ relations D Sc cutoff i v w) :
    movingPower D Sc cutoff i v 1 ≫ h ∈ relations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, movingDot_insert, Category.assoc]
    exact Submodule.subset_span ⟨t, _, twist_ideal D Sc cutoff _ hr, _, rfl⟩
  | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

/-- Unlike cancellation, preservation holds for the unsquared moving dot. -/
theorem projection_source_difference_zero (i : I) (v z : List I) (a : ℕ)
    (h : hom D Sc cutoff (i :: v) z) (hh : projection D Sc cutoff i v z h = 0) :
    projection D Sc cutoff i v z
      ((sourceDotPower D Sc cutoff (i :: v) (a + 1) 1 -
        sourceDotPower D Sc cutoff (i :: v) 0 1) ≫ h) = 0 := by
  have ho := congrArg (oldSourceTarget D Sc cutoff i v z (sourceDotPower D Sc cutoff v a 1)) hh
  rw [map_zero] at ho
  change projection D Sc cutoff i v z
    (insert D Sc cutoff i v v (sourceDotPower D Sc cutoff v a 1) ≫ h) = 0 at ho
  rw [insert_sourceDotPower] at ho
  have hm : projection D Sc cutoff i v z (movingPower D Sc cutoff i v 1 ≫ h) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero (relations D Sc cutoff i v z)).mpr
    exact movingDot_relations D Sc cutoff i
      ((Submodule.Quotient.mk_eq_zero (relations D Sc cutoff i v z)).mp hh)
  rw [Preadditive.sub_comp, map_sub, ho]
  exact sub_eq_zero.mpr hm.symm

/-- Cancel a positive even-parity source power against an arbitrary old positioned power. -/
theorem projection_power_difference_cancel (i : I) (v z : List I) (a d : ℕ)
    (hd : d • D.parity i = 0) (hpos : 0 < d) (h : hom D Sc cutoff (i :: v) z)
    (hh : projection D Sc cutoff i v z
      ((sourceDotPower D Sc cutoff (i :: v) (a + 1) d -
        sourceDotPower D Sc cutoff (i :: v) 0 d) ≫ h) = 0) :
    projection D Sc cutoff i v z h = 0 := by
  apply movingPower_eq_oldSource D Sc cutoff 0 i v z d hd hpos
    (sourceDotPower D Sc cutoff v a d)
  change projection D Sc cutoff i v z (movingPower D Sc cutoff i v d ≫ h) =
    projection D Sc cutoff i v z (insert D Sc cutoff i v v (sourceDotPower D Sc cutoff v a d) ≫ h)
  rw [insert_sourceDotPower]
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hh
  exact hh.symm

private theorem rightContext_affineUnit_dotPower (i : I) (μ σ : List I) (b d : ℕ)
    (hb : b < (i :: μ).length) :
    rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ) (dotE D Sc (i :: μ) b ^ d)) =
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) b d := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    (whiskerWordRingHom D Sc (i :: μ) σ (dotE D Sc (i :: μ) b ^ d)) = _
  rw [map_pow, whiskerWordRingHom_apply, dotE_whiskerRight D Sc (i :: μ) σ b hb]
  rfl

private theorem qpEval_power_difference (i : I) (μ σ z : List I) (a d : ℕ)
    (ha : a < μ.length) (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ)))) :
    qpEval D Sc cutoff i μ σ z h
      ((dotE D Sc (i :: μ) (a + 1) ^ d - dotE D Sc (i :: μ) 0 ^ d) ≫ f) =
    projection D Sc cutoff i (μ ++ σ) z
      ((sourceDotPower D Sc cutoff (i :: (μ ++ σ)) (a + 1) d -
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) 0 d) ≫
        (rightContext D Sc cutoff σ _ _ (affineUnit D Sc cutoff _ _ f) ≫
          (relation D Sc cutoff i (μ ++ σ) ≫ h))) := by
  change projection D Sc cutoff i (μ ++ σ) z
    (rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ)
        ((dotE D Sc (i :: μ) (a + 1) ^ d - dotE D Sc (i :: μ) 0 ^ d) ≫ f)) ≫
      (relation D Sc cutoff i (μ ++ σ) ≫ h)) = _
  rw [affineUnit_comp, rightContext_comp, Category.assoc]
  have he : rightContext D Sc cutoff σ (i :: μ) (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ)
        (dotE D Sc (i :: μ) (a + 1) ^ d - dotE D Sc (i :: μ) 0 ^ d)) =
      sourceDotPower D Sc cutoff (i :: (μ ++ σ)) (a + 1) d -
        sourceDotPower D Sc cutoff (i :: (μ ++ σ)) 0 d := by
    rw [map_sub, map_sub,
      rightContext_affineUnit_dotPower D Sc cutoff i μ σ (a + 1) d (by simp; omega),
      rightContext_affineUnit_dotPower D Sc cutoff i μ σ 0 d (by simp)]
  rw [he]

/-- Square cancellation for `qpEval` in arbitrary right contexts. -/
theorem qpEval_square_difference_cancel (i : I) (μ σ z : List I) (a : ℕ)
    (ha : a < μ.length) (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ))))
    (hf : qpEval D Sc cutoff i μ σ z h
      ((dotE D Sc (i :: μ) (a + 1) ^ 2 - dotE D Sc (i :: μ) 0 ^ 2) ≫ f) = 0) :
    qpEval D Sc cutoff i μ σ z h f = 0 := by
  rw [qpEval_power_difference D Sc cutoff i μ σ z a 2 ha] at hf
  exact projection_power_difference_cancel D Sc cutoff i (μ ++ σ) z a 2
    ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) _) (by decide) _ hf

/-- The odd source difference preserves zero evaluation, using total-parity naturality. -/
theorem qpEval_source_difference_zero (i : I) (μ σ z : List I) (a : ℕ)
    (ha : a < μ.length) (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ))))
    (hf : qpEval D Sc cutoff i μ σ z h f = 0) :
    qpEval D Sc cutoff i μ σ z h
      ((dotE D Sc (i :: μ) (a + 1) - dotE D Sc (i :: μ) 0) ≫ f) = 0 := by
  have he := qpEval_power_difference D Sc cutoff i μ σ z a 1 ha h f
  simp only [pow_one] at he
  rw [he]
  exact projection_source_difference_zero D Sc cutoff i (μ ++ σ) z a _ hf

/-- The full-coefficient all-prefix relation in evaluation coordinates. -/
theorem qpEval_prefix_zero (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: (μ ++ [i])) ++ σ) z) :
    qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) = 0 := by
  have hK := allPrefix_relation_context D Sc cutoff i μ σ z h
  change projection D Sc cutoff i ((μ ++ [i]) ++ σ) z
    (rightContext D Sc cutoff σ (i :: (μ ++ [i])) (i :: (μ ++ [i]))
      (affineUnit D Sc cutoff (i :: (μ ++ [i])) ((μ ++ [i]) ++ [i])
        (moveHom D Sc i [] (μ ++ [i])) ≫
        affineUnit D Sc cutoff ((μ ++ [i]) ++ [i]) (i :: (μ ++ [i]))
          (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) ≫
      relation D Sc cutoff i ((μ ++ [i]) ++ σ) ≫ h) = 0 at hK
  rw [← affineUnit_comp D Sc cutoff
    (v := i :: (μ ++ [i])) (w := (μ ++ [i]) ++ [i]) (z := i :: (μ ++ [i]))
    (moveHom D Sc i [] (μ ++ [i]))
    (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))] at hK
  exact hK

private theorem odd_expansion {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {x y : C} (Δ E : End x) (V : x ⟶ y) (τ : End y) (T : y ⟶ x) (s : k) :
    Δ ≫ (s • (E ≫ (V ≫ T)) - Δ ≫ (V ≫ (τ ≫ T))) =
      (s • (Δ ≫ E ≫ V) - Δ ≫ Δ ≫ V ≫ τ) ≫ T := by
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Linear.comp_smul,
    Linear.smul_comp, Category.assoc]

/-- Repeated-odd recursion. Both prefix signs are retained until their product is one.
The new last letter makes the old word nonempty even when the prefix is empty. -/
theorem qp_repeated_odd (i : I) (hi : D.parity i = 1) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: (μ ++ [i])) ++ σ) z) :
    qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫ lastToFirstHom D Sc i (μ ++ [i])) =
    qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (((dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) -
        dotE D Sc (i :: (μ ++ [i])) 0) ^ 2) ≫
        moveWhisker D Sc i μ ≫
          (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) := by
  let E := dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) -
    dotE D Sc (i :: (μ ++ [i])) 0
  let Δ := dotE D Sc (i :: (μ ++ [i])) (μ.length + 1) ^ 2 -
    dotE D Sc (i :: (μ ++ [i])) 0 ^ 2
  let s := SKM.zsign k (D.parity i * wordSumParity D μ)
  let A : End ((pres D Sc).obj (ob D (i :: (μ ++ [i])))) :=
    moveWhisker D Sc i μ ≫ (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))
  let B := moveWhisker D Sc i μ ≫ lastToFirstHom D Sc i (μ ++ [i])
  have hK := qpEval_prefix_zero D Sc cutoff i μ σ z h
  have hzero : qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (Δ ≫ (s • (E ≫ A) - Δ ≫ B)) = 0 := by
    change qpEval D Sc cutoff i (μ ++ [i]) σ z h
      (moveHom D Sc i [] (μ ++ [i]) ≫
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i]))) = 0 at hK
    rw [moveHom_append_self, moveWhisker_comp_sameIntertwiner_odd D Sc i hi μ] at hK
    dsimp only [A, B]
    rw [lastToFirstHom_append_self]
    exact (congrArg (qpEval D Sc cutoff i (μ ++ [i]) σ z h)
      (odd_expansion Δ E (moveWhisker D Sc i μ)
        (crossE D Sc (μ ++ [i] ++ [i]) μ.length)
        (lastToFirstHom D Sc i μ ▷ (pres D Sc).obj (ob D [i])) s)).trans hK
  have hc := qpEval_square_difference_cancel D Sc cutoff i (μ ++ [i]) σ z μ.length
    (by simp) h (s • (E ≫ A) - Δ ≫ B) hzero
  have hp := qpEval_source_difference_zero D Sc cutoff i (μ ++ [i]) σ z μ.length
    (by simp) h (s • (E ≫ A) - Δ ≫ B) hc
  have hDE : Δ * E = E * Δ :=
    squareDiff_mul_sub_comm (dotE_last_mul_first D Sc i μ) (zsign_mul_self _)
  have hED : E ≫ Δ ≫ B = Δ ≫ E ≫ B := by
    rw [← Category.assoc E Δ B, ← Category.assoc Δ E B]
    exact congrArg (fun f : End ((pres D Sc).obj (ob D (i :: (μ ++ [i])))) => f ≫ B) hDE
  change qpEval D Sc cutoff i (μ ++ [i]) σ z h (E ≫ (s • (E ≫ A) - Δ ≫ B)) = 0 at hp
  rw [Preadditive.comp_sub, Linear.comp_smul, hED, map_sub, map_smul, sub_eq_zero] at hp
  rw [moveHom_lastToFirstHom_append_self_odd D Sc i hi μ, map_smul]
  change s • qpEval D Sc cutoff i (μ ++ [i]) σ z h (Δ ≫ E ≫ B) = _
  rw [← hp, smul_smul, show s * s = 1 from zsign_mul_self _, one_smul]
  congr 1
  simp only [E, A, pow_two, End.mul_def, Category.assoc]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# QP right-context descent over ELV coefficients

Supporting steps for `DeformedGlobalQP.md` §3, in the library's signed crossing
convention. Spectator extension descends to the old-only quotient, with the full
coefficient algebra unchanged. The distinct-colour recursion and empty-word base
use the same evaluation as the repeated-colour recursions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Right spectators preserve the defining relation submodule, not merely the old ideal. -/
theorem relations_rightContext (σ : List I) (i : I) {v w : List I}
    {f : hom D Sc cutoff (i :: v) w} (hf : f ∈ relations D Sc cutoff i v w) :
    rightContext D Sc cutoff σ (i :: v) w f ∈
      relations D Sc cutoff i (v ++ σ) (w ++ σ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t, r, hr, h, rfl⟩ := hf
    rw [rightContext_comp, rightContext_insert]
    exact Submodule.subset_span ⟨t ++ σ, _, ideal_rightContext D Sc cutoff σ hr, _, rfl⟩
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

/-- Spectator extension on the old-only quotient. -/
def targetRightContext (σ : List I) (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i (v ++ σ) (w ++ σ) :=
  (relations D Sc cutoff i v w).mapQ
    (relations D Sc cutoff i (v ++ σ) (w ++ σ))
    (rightContext D Sc cutoff σ (i :: v) w)
    (fun _ hf => relations_rightContext D Sc cutoff σ i hf)

@[simp] theorem targetRightContext_projection (σ : List I) (i : I) (v w : List I)
    (f : hom D Sc cutoff (i :: v) w) :
    targetRightContext D Sc cutoff σ i v w (projection D Sc cutoff i v w f) =
      projection D Sc cutoff i (v ++ σ) (w ++ σ)
        (rightContext D Sc cutoff σ (i :: v) w f) := rfl

/-- Distinct-colour recursion, with arbitrary spectators and full ELV continuation. -/
theorem qp_distinct (i x : I) (hx : i ≠ x) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: (μ ++ [x])) ++ σ) z) :
    qpEval D Sc cutoff i (μ ++ [x]) σ z h
      (moveHom D Sc i [] (μ ++ [x]) ≫ lastToFirstHom D Sc i (μ ++ [x])) =
    qpEval D Sc cutoff i (μ ++ [x]) σ z h
      (qPoly D Sc (dotE D Sc (i :: (μ ++ [x])) 0)
        (dotE D Sc (i :: (μ ++ [x])) (μ.length + 1)) i x ≫
        ((moveHom D Sc i [] μ ≫ lastToFirstHom D Sc i μ) ▷ (pres D Sc).obj (ob D [x]))) := by
  rw [moveHom_lastToFirstHom_append_ne D Sc hx μ]

/-- Empty-word base with the actual signed product and arbitrary continuation. -/
theorem qp_nil (i : I) (σ z : List I) (h : hom D Sc cutoff (i :: σ) z) :
    qpEval D Sc cutoff i [] σ z h
      (moveHom D Sc i [] [] ≫ lastToFirstHom D Sc i []) =
      qpEval D Sc cutoff i [] σ z h (qpProduct D Sc i []) := by
  congr 1
  simp [moveHom, lastToFirstHom, qpProduct, End.one_def]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Signed QP product over the full ELV coefficient algebra

The all-word identity of `DeformedGlobalQP.md` §3 follows by reverse-word induction.
Polynomial factors preserve the defining relation span; right-context descent and
typed empty-context transport connect the three recursions to the induction.
The existing `qpProduct` is unchanged, including each repeated-even factor `−1`.
No restriction on colours, coefficients, or cutoffs is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem affineUnit_id (v : List I) :
    affineUnit D Sc cutoff v v (𝟙 ((pres D Sc).obj (ob D v))) =
      𝟙 (obj D Sc cutoff v) := rfl

def relationPreserving (i : I) (v : List I) :
    Subalgebra k (End ((pres D Sc).obj (ob D (i :: v)))) where
  carrier := {f | ∀ (w : List I) (h : hom D Sc cutoff (i :: v) w),
    h ∈ relations D Sc cutoff i v w →
    affineUnit D Sc cutoff _ _ f ≫ h ∈ relations D Sc cutoff i v w}
  mul_mem' hf hg w h hh := by
    rw [End.mul_def, affineUnit_comp, Category.assoc]
    exact hg w _ (hf w h hh)
  add_mem' hf hg w h hh := by
    rw [map_add, Preadditive.add_comp]
    exact Submodule.add_mem _ (hf w h hh) (hg w h hh)
  algebraMap_mem' c w h hh := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Linear.smul_comp]
    rw [End.one_def, affineUnit_id, Category.id_comp]
    exact Submodule.smul_mem _ c hh

theorem affineUnit_dot (v : List I) (b : ℕ) :
    affineUnit D Sc cutoff v v (dotE D Sc v b) = sourceDotPower D Sc cutoff v b 1 := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] dotE D Sc v b =
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] (dotE D Sc v b ^ 1)
  rw [pow_one]

theorem dot_mem_relationPreserving (i : I) (v : List I) (b : ℕ) :
    dotE D Sc (i :: v) b ∈ relationPreserving D Sc cutoff i v := by
  intro w h hh
  rw [affineUnit_dot]
  cases b with
  | zero => exact movingDot_relations D Sc cutoff i hh
  | succ b =>
    have hz : projection D Sc cutoff i v w h = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hh
    have he := congrArg (oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b 1)) hz
    rw [map_zero] at he
    change projection D Sc cutoff i v w
      (insert D Sc cutoff i v v (sourceDotPower D Sc cutoff v b 1) ≫ h) = 0 at he
    rw [insert_sourceDotPower] at he
    exact (Submodule.Quotient.mk_eq_zero _).mp he

theorem qpFactor_mem_relationPreserving (i : I) (v : List I) (x : I) (b : ℕ) :
    qpFactor D Sc i v x b ∈ relationPreserving D Sc cutoff i v := by
  let A := relationPreserving D Sc cutoff i v
  have h0 := dot_mem_relationPreserving D Sc cutoff i v 0
  have hb := dot_mem_relationPreserving D Sc cutoff i v (b + 1)
  unfold qpFactor
  split_ifs
  · exact A.pow_mem (A.sub_mem hb h0) 2
  · exact A.neg_mem A.one_mem
  · unfold qPoly
    split_ifs
    · exact A.smul_mem A.one_mem _
    · exact A.add_mem (A.sum_mem fun p _ => A.sum_mem fun q _ =>
        A.smul_mem (A.mul_mem (A.pow_mem h0 p) (A.pow_mem hb q)) _)
        (A.add_mem (A.smul_mem (A.pow_mem h0 _) _) (A.smul_mem (A.pow_mem hb _) _))

theorem projection_precomp_eq (i : I) (v w : List I)
    (a : End ((pres D Sc).obj (ob D (i :: v))))
    (ha : a ∈ relationPreserving D Sc cutoff i v)
    (f g : hom D Sc cutoff (i :: v) w)
    (he : projection D Sc cutoff i v w f = projection D Sc cutoff i v w g) :
    projection D Sc cutoff i v w (affineUnit D Sc cutoff _ _ a ≫ f) =
      projection D Sc cutoff i v w (affineUnit D Sc cutoff _ _ a ≫ g) := by
  have he' : f - g ∈ relations D Sc cutoff i v w := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change projection D Sc cutoff i v w (f - g) = 0
    rw [map_sub, he, sub_self]
  have hz := (Submodule.Quotient.mk_eq_zero _).mpr (ha w (f - g) he')
  change projection D Sc cutoff i v w (affineUnit D Sc cutoff _ _ a ≫ (f - g)) = 0 at hz
  rw [Preadditive.comp_sub, map_sub, sub_eq_zero] at hz
  exact hz

private theorem affineRightContext_nil (v w : List I)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    affineRightContext D Sc [] v w f =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (List.append_nil v)) ≫
        f ≫ eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (List.append_nil w)).symm := by
  have ht : f ▷ (𝟙_ (pres D Sc).Presented) =
      (ρ_ ((pres D Sc).obj (ob D v))).hom ≫ f ≫
        (ρ_ ((pres D Sc).obj (ob D w))).inv := by
    rw [← Category.assoc, ← MonoidalSupercategory.rightUnitor_naturality (R := k)]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact ht
private theorem qpEval_apply_empty_aux (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ)))) :
    qpEval D Sc cutoff i μ σ z h f =
    projection D Sc cutoff i (μ ++ σ) z
      (rightContext D Sc cutoff σ (i :: μ) (i :: μ)
        (affineUnit D Sc cutoff _ _ f) ≫ (relation D Sc cutoff i (μ ++ σ) ≫ h)) := rfl

private theorem rightContext_affineUnit_aux (σ v w : List I)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    rightContext D Sc cutoff σ v w (affineUnit D Sc cutoff v w f) =
    affineUnit D Sc cutoff (v ++ σ) (w ++ σ) (affineRightContext D Sc σ v w f) := rfl

private theorem projection_transport_aux (i : I) (μ ν : List I) (e : ν = μ)
    (f g : End ((pres D Sc).obj (ob D (i :: μ))))
    (he : projection D Sc cutoff i ν (i :: μ)
      (affineUnit D Sc cutoff (i :: ν) (i :: ν)
        (eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e) ≫ f ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e).symm) ≫
        (relation D Sc cutoff i ν ≫
          eqToHom (congrArg (fun t => obj D Sc cutoff (i :: t)) e))) =
      projection D Sc cutoff i ν (i :: μ)
      (affineUnit D Sc cutoff (i :: ν) (i :: ν)
        (eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e) ≫ g ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e).symm) ≫
        (relation D Sc cutoff i ν ≫
          eqToHom (congrArg (fun t => obj D Sc cutoff (i :: t)) e)))) :
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ) f ≫ relation D Sc cutoff i μ) =
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ) g ≫ relation D Sc cutoff i μ) := by
  subst ν
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using he

private theorem projection_eq_of_qpEval_eq (i : I) (μ : List I)
    (f g : End ((pres D Sc).obj (ob D (i :: μ))))
    (he : ∀ σ z (h : hom D Sc cutoff ((i :: μ) ++ σ) z),
      qpEval D Sc cutoff i μ σ z h f = qpEval D Sc cutoff i μ σ z h g) :
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff _ _ f ≫ relation D Sc cutoff i μ) =
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff _ _ g ≫ relation D Sc cutoff i μ) := by
  have hh := he [] (i :: μ)
    (eqToHom (congrArg (obj D Sc cutoff) (List.append_nil (i :: μ))))
  rw [qpEval_apply_empty_aux, qpEval_apply_empty_aux,
    rightContext_affineUnit_aux, rightContext_affineUnit_aux,
    affineRightContext_nil, affineRightContext_nil] at hh
  exact projection_transport_aux D Sc cutoff i μ (μ ++ []) (List.append_nil μ) f g hh
/-- Extend an equality after the first-position relation by an arbitrary word.
No quotient-target transports and no restrictions on coefficients are necessary. -/
theorem projection_affine_whiskerRight_eq (i : I) (μ τ : List I)
    (f g : End ((pres D Sc).obj (ob D (i :: μ))))
    (hfg : projection D Sc cutoff i μ (i :: μ)
        (affineUnit D Sc cutoff _ _ f ≫ relation D Sc cutoff i μ) =
      projection D Sc cutoff i μ (i :: μ)
        (affineUnit D Sc cutoff _ _ g ≫ relation D Sc cutoff i μ)) :
    projection D Sc cutoff i (μ ++ τ) (i :: (μ ++ τ))
        (affineUnit D Sc cutoff _ _ (f ▷ (pres D Sc).obj (ob D τ)) ≫
          relation D Sc cutoff i (μ ++ τ)) =
      projection D Sc cutoff i (μ ++ τ) (i :: (μ ++ τ))
        (affineUnit D Sc cutoff _ _ (g ▷ (pres D Sc).obj (ob D τ)) ≫
          relation D Sc cutoff i (μ ++ τ)) := by
  have he := congrArg (targetRightContext D Sc cutoff τ i μ (i :: μ)) hfg
  simp only [targetRightContext_projection, rightContext_comp,
    rightContext_relation] at he
  exact he

/-- Raw projected all-word identity, before adjoining spectators. -/
theorem qp_projection_product (i : I) (μ : List I) :
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff _ _ (moveHom D Sc i [] μ ≫ lastToFirstHom D Sc i μ) ≫
        relation D Sc cutoff i μ) =
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i μ) ≫ relation D Sc cutoff i μ) := by
  induction μ using List.reverseRecOn with
  | nil =>
    apply projection_eq_of_qpEval_eq
    exact fun σ z h => qp_nil D Sc cutoff i σ z h
  | append_singleton μ x ih =>
    have he := projection_affine_whiskerRight_eq D Sc cutoff i μ [x] _ _ ih
    have hf := projection_precomp_eq D Sc cutoff i (μ ++ [x]) (i :: (μ ++ [x]))
      (qpFactor D Sc i (μ ++ [x]) x μ.length)
      (qpFactor_mem_relationPreserving D Sc cutoff i (μ ++ [x]) x μ.length) _ _ he
    rw [← Category.assoc, ← Category.assoc, ← affineUnit_comp, ← affineUnit_comp] at hf
    rw [qpProduct_append, End.mul_def]
    refine Eq.trans ?_ hf
    apply projection_eq_of_qpEval_eq
    intro σ z h
    rw [MonoidalSupercategory.comp_whiskerRight (R := k)]
    by_cases hx : x = i
    · subst x
      rcases parity_eq_zero_or_one (D.parity i) with hi | hi
      · have hr := qp_repeated_even D Sc cutoff i hi μ σ z h
        rw [qpFactor, ite_eq_left rfl, ite_eq_right (by simp [hi]), End.one_def,
          Preadditive.neg_comp, Category.id_comp, map_neg]
        exact hr
      · have hr := qp_repeated_odd D Sc cutoff i hi μ σ z h
        simpa only [qpFactor, ite_eq_left rfl, hi, ite_eq_left,
          MonoidalSupercategory.comp_whiskerRight, moveWhisker, Category.assoc] using hr
    · have hr := qp_distinct D Sc cutoff i x (Ne.symm hx) μ σ z h
      rw [MonoidalSupercategory.comp_whiskerRight (R := k)] at hr
      simpa only [qpFactor, ite_eq_right hx] using hr

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Signed moving-power coordinates

Every unsigned moving dot power descends through the old cyclotomic relations.
Its coordinate action shifts the moving exponent and applies the total-parity
involution to the old coefficient. The exact coordinate and support bound are
inputs to signed polynomial regularity; no parity-zero restriction is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem movingPower_succ_comp (i : I) (v : List I) (d : ℕ) :
    movingPower D Sc cutoff i v (d + 1) =
      movingPower D Sc cutoff i v 1 ≫ movingPower D Sc cutoff i v d := by
  change affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ (d + 1) : End _) =
    affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ 1 : End _) ≫
      affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ d : End _)
  rw [pow_succ, End.mul_def, affineUnit_comp, pow_one]

theorem movingPower_insert_twist (i : I) {v t : List I} (d : ℕ)
    (r : hom D Sc cutoff v t) :
    movingPower D Sc cutoff i v d ≫ insert D Sc cutoff i v t r =
      insert D Sc cutoff i v t (twist k (d • D.parity i) r) ≫
        movingPower D Sc cutoff i t d := by
  induction d with
  | zero =>
    change (𝟙 (obj D Sc cutoff (i :: v))) ≫ insert D Sc cutoff i v t r =
      insert D Sc cutoff i v t (twist k (0 • D.parity i) r) ≫ 𝟙 _
    simp
  | succ d ih =>
    rw [movingPower_succ_comp, Category.assoc, ih, ← Category.assoc,
      movingDot_insert, Category.assoc, ← movingPower_succ_comp]
    rw [← twist_add, succ_nsmul, add_comm]

/-- Every moving power preserves the old cyclotomic relations. -/
theorem movingPower_relations_twist (i : I) {v w : List I} (d : ℕ)
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    movingPower D Sc cutoff i v d ≫ h ∈ relations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, movingPower_insert_twist, Category.assoc]
    exact Submodule.subset_span ⟨t, _, twist_ideal D Sc cutoff _ hr, _, rfl⟩
  | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

/-- Unsigned moving powers on the quotient, without a parity restriction. -/
def signedMovingPowerTarget (i : I) (v w : List I) (d : ℕ) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (relations D Sc cutoff i v w)
    (Linear.leftComp k _ (movingPower D Sc cutoff i v d))
    (fun _ hh => movingPower_relations_twist D Sc cutoff i d hh)

@[simp] theorem signedMovingPowerTarget_projection (i : I) (v w : List I) (d : ℕ)
    (h : hom D Sc cutoff (i :: v) w) :
    signedMovingPowerTarget D Sc cutoff i v w d (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w (movingPower D Sc cutoff i v d ≫ h) := rfl

private theorem movingPower_tail_shift {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) :
    movingPower D Sc cutoff i x.oldTarget d ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x :
        hom D Sc cutoff (i :: x.oldTarget) w) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc (x.shift d) : hom D Sc cutoff (i :: x.oldTarget) w) := by
  change affineUnit D Sc cutoff _ _ _ ≫ affineUnit D Sc cutoff _ _ _ =
    affineUnit D Sc cutoff _ _ _
  rw [← affineUnit_comp, prependTail_shift]

/-- The signed coefficient shift for the unsigned moving operator. -/
theorem signedMovingPower_pair_shift (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (b : Old D Sc cutoff v x.oldTarget) :
    signedMovingPowerTarget D Sc cutoff i v w d
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc (x.shift d))
        (oldTwist D Sc cutoff (d • D.parity i) v x.oldTarget b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  let h : hom D Sc cutoff (i :: x.oldTarget) w :=
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x
  let h' : hom D Sc cutoff (i :: x.oldTarget) w :=
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc (x.shift d)
  change projection D Sc cutoff i v w
    (movingPower D Sc cutoff i v d ≫ (insert D Sc cutoff i v x.oldTarget (twist k p r) ≫ h)) =
    projection D Sc cutoff i v w
      (insert D Sc cutoff i v x.oldTarget (twist k p (twist k (d • D.parity i) r)) ≫ h')
  apply congrArg (projection D Sc cutoff i v w)
  calc
    _ = (movingPower D Sc cutoff i v d ≫
        insert D Sc cutoff i v x.oldTarget (twist k p r)) ≫ h :=
      (Category.assoc _ _ _).symm
    _ = (insert D Sc cutoff i v x.oldTarget (twist k (d • D.parity i) (twist k p r)) ≫
        movingPower D Sc cutoff i x.oldTarget d) ≫ h :=
      congrArg (fun a => a ≫ h) (movingPower_insert_twist D Sc cutoff i d _)
    _ = insert D Sc cutoff i v x.oldTarget (twist k (d • D.parity i) (twist k p r)) ≫
        (movingPower D Sc cutoff i x.oldTarget d ≫ h) := Category.assoc _ _ _
    _ = insert D Sc cutoff i v x.oldTarget (twist k (d • D.parity i) (twist k p r)) ≫ h' :=
      congrArg (fun a => insert D Sc cutoff i v x.oldTarget
        (twist k (d • D.parity i) (twist k p r)) ≫ a) (movingPower_tail_shift D Sc cutoff x d)
    _ = _ := by rw [← twist_add, ← twist_add, add_comm p]

/-- Simultaneous coordinates detect the shifted coefficient for every finite coordinate vector. -/
theorem signedMovingPower_coordinate_shift (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (d : ℕ)
    (f : PrependOldCoordinates D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d
        (prependOldReconstruct D Sc cutoff p i v w f)) = oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget (f q) := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply, map_add]
  | of t b =>
    change prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d
        (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t b))) = _
    rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift]
    by_cases ht : t = q
    · subst t
      erw [prependOldCoordinate_pair, DirectSum.of_eq_same]
    · erw [prependOldCoordinate_pair_off]
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht), map_zero]
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

/-- Exact shifted coordinate of an arbitrary quotient element. -/
theorem signedMovingPower_coordinate (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (d : ℕ) (z : Target D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d z) =
      oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget
        (prependOldCoordinateEquiv D Sc cutoff p i v w z q) := by
  simpa only [prependOldReconstruct_coordinateEquiv] using
    signedMovingPower_coordinate_shift D Sc cutoff p q d
      (prependOldCoordinateEquiv D Sc cutoff p i v w z)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-!
# Regularity of the moving cyclotomic relation

The explicit odd ELV and even monic coefficients express the moving relation
as its top unsigned moving power plus lower powers with old coefficient actions.
At a maximal moving-support coordinate the lower terms vanish. The top term
is the total-parity involution of the original coefficient, hence detects it.
This proves cancellation in the old-only quotient over arbitrary commutative
rings, including zero cutoffs, without flatness or nonvanishing hypotheses.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem movingPower_oldSource_above (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (c : hom D Sc cutoff v v)
    (f : PrependOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    prependOldCoordinate D Sc cutoff p x
      (signedMovingPowerTarget D Sc cutoff i v w d
        (oldSourceTarget D Sc cutoff i v w c
          (prependOldReconstruct D Sc cutoff p i v w f))) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [prependOldReconstruct, DirectSum.toModule_lof, oldSourceTarget_pair,
    signedMovingPower_pair_shift]
  apply prependOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega

theorem movingPower_comp_coefficient (i : I) (v : List I) (d : ℕ)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    movingPower D Sc cutoff i v d ≫
      insert D Sc cutoff i v v (a ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D v))) =
      (a ⊗ₜ[k] (dotE D Sc (i :: v) 0 ^ d : End _)) := by
  rw [insert_tmul]
  have hi : affineInsert D Sc i v v (𝟙 _) = 𝟙 _ :=
    MonoidalSupercategory.whiskerLeft_id (R := k)
      ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D v))
  rw [hi]
  change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
    (Y := obj D Sc cutoff (i :: v)) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
        (Y := obj D Sc cutoff (i :: v)) a (𝟙 _) = _
  rw [BoxProd.tmulHom_comp_tmulHom
    (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: v))
    (Z := obj D Sc cutoff (i :: v))
    (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
      SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem)
    _ a (id_mem (R := k) _)]
  simp only [koszulSign_zero_left, one_smul, Category.comp_id]
  change (a * 1) ⊗ₜ[k] _ = _
  rw [mul_one]

theorem deformedCyclotomic_expansion (i : I) (v : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) :
    (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) =
      ∑ j : Fin (N + 1), movingPower D Sc cutoff i v j.val ≫
        insert D Sc cutoff i v v
          (SKM.SYM.elvCoefficientQuotient D cutoff (c j) ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D v))) := by
  change elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc (i :: v) N c) = _
  unfold deformedCyclotomic
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [elvQuotientMap_source, movingPower_comp_coefficient]
  congr 1
  simp only [firstDotPower, dotE_pow, List.map_replicate]

theorem oldSourceTarget_projection (i : I) (v w : List I) (c : hom D Sc cutoff v v)
    (h : hom D Sc cutoff (i :: v) w) :
    oldSourceTarget D Sc cutoff i v w c (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w (insert D Sc cutoff i v v c ≫ h) := rfl

theorem oldSourceTarget_id (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    oldSourceTarget D Sc cutoff i v w (𝟙 _) z = z := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change projection D Sc cutoff i v w (insert D Sc cutoff i v v (𝟙 _) ≫ h) = _
  rw [insert_id, Category.id_comp]

/-- Finite moving support proves cancellation for a polynomial whose top coefficient is one. -/
theorem monic_moving_sum_regular (i : I) (v w : List I) (N : ℕ)
    (c : Fin (N + 1) → hom D Sc cutoff v v) (hc : c (Fin.last N) = 𝟙 _)
    (z : Target D Sc cutoff i v w)
    (hz : (∑ j : Fin (N + 1), signedMovingPowerTarget D Sc cutoff i v w j.val
      (oldSourceTarget D Sc cutoff i v w (c j) z)) = 0) : z = 0 := by
  let f := prependOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  rw [Fin.sum_univ_castSucc, hc, oldSourceTarget_id] at hz
  have he := congrArg (prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)) hz
  rw [map_add, map_sum, map_zero] at he
  have hl : (∑ j : Fin N, prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)
      (signedMovingPowerTarget D Sc cutoff i v w j.val
        (oldSourceTarget D Sc cutoff i v w (c j.castSucc) z))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hb : ∀ t ∈ f.support, j.val + t.1.1 < (q.representative.shift N).1.1 := by
      intro t ht
      have hm := hmax t ht
      have hk := congrArg Prod.fst q.representative_tailKey
      change q.representative.1.1 = q.1.1 at hk
      change j.val + t.1.1 < N + q.representative.1.1
      have hj := j.isLt
      omega
    simpa only [f, prependOldReconstruct_coordinateEquiv] using
      movingPower_oldSource_above D Sc cutoff 0 (q.representative.shift N)
        j.val (c j.castSucc) f hb
  change (∑ j : Fin N, prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)
      (signedMovingPowerTarget D Sc cutoff i v w j.val
        (oldSourceTarget D Sc cutoff i v w (c j.castSucc) z))) +
      prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)
        (signedMovingPowerTarget D Sc cutoff i v w N z) = 0 at he
  rw [hl, zero_add, signedMovingPower_coordinate] at he
  have hh := congrArg (oldTwist D Sc cutoff (N • D.parity i) v q.representative.oldTarget) he
  rw [oldTwist_twice, map_zero] at hh
  exact (DFinsupp.mem_support_iff.mp hq) hh

/-- Cancellation for the explicit coefficient-valued monic polynomial. -/
theorem projection_deformedCyclotomic_regular (i : I) (v w : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) (hc : c (Fin.last N) = 1)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      ((elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  apply monic_moving_sum_regular D Sc cutoff i v w N
    (fun j => SKM.SYM.elvCoefficientQuotient D cutoff (c j) ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D v)))
  · rw [hc, map_one]
    rfl
  · rw [deformedCyclotomic_expansion, Preadditive.sum_comp, map_sum] at hh
    simpa only [oldSourceTarget_projection, signedMovingPowerTarget_projection, Category.assoc] using hh

/-- The moving cyclotomic relation is regular on the old-only quotient over every commutative ring. -/
theorem projection_relation_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w (relation D Sc cutoff i v ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  unfold relation at hh
  split_ifs at hh with hi
  · exact projection_deformedCyclotomic_regular D Sc cutoff i v w (cutoff i)
      (SKM.SYM.elvMonicCoefficient D k ⟨i, hi⟩ (cutoff i))
      (SKM.SYM.elvMonicCoefficient_top D k ⟨i, hi⟩ (cutoff i)) h hh
  · exact projection_deformedCyclotomic_regular D Sc cutoff i v w (cutoff i)
      (SKM.SYM.evenMonicCoefficient D k i (cutoff i))
      (SKM.SYM.evenMonicCoefficient_top D k i (cutoff i)) h hh

end OddMath.QuiverHecke.ELVOld
end

end
