import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSpecialization
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModule
import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicSpan
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight
import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyTarget
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerGrading
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetDot
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.SkewPolynomial.Basic
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerGrading
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTargetDot
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.Ring.TransferInstance

/-! # Scalar probe specialization of the untruncated ELV content ring
This supplies the ring input for the probe-factor base change of
InvertibleDotProbe.md Sections 1 and 5. The source is the untruncated
ELVOld.ContentRing. The target uses the existing heightAlgebra, including
the vacuum height. Module-action and prescribed inverse-matrix comparison
are separate.
-/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.QuiverHecke.CyclotomicAction
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (m : I → ℕ) (Sc : SKM.Scalars D k) [Fintype I]
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

/-- The existing affine/cyclotomic quotient map at every height. -/
def probeHeightMk : (n : ℕ) → Hn D Sc n →ₐ[k] heightAlgebra D Sc a n
  | 0 => AlgHom.id k _
  | n+1 => cyclotomicMk D Sc a n

private def probeHeightAffineEntry {n : ℕ} (s t : Word I n) :
    ((pres D Sc).obj (ob D s.val) ⟶ (pres D Sc).obj (ob D t.val)) →ₗ[k]
      heightAlgebra D Sc a n where
  toFun f := probeHeightMk D m Sc n (FiniteHomMatrix.single t s f)
  map_add' f g := by
    rw [FiniteHomMatrix.single_add, map_add]
  map_smul' c f := by
    rw [FiniteHomMatrix.single_smul, map_smul]
    rfl

private def elvProbeHeightRawEntry {n : ℕ} (s t : Word I n) :
    ELVOld.hom D Sc cut s.val t.val →ₗ[k] heightAlgebra D Sc a n :=
  (probeHeightAffineEntry D m Sc s t).comp (elvProbeScalarHom D m Sc s.val t.val)

private theorem elvProbeHeightRawEntry_ideal {n : ℕ} (s t : Word I n)
    (f : ELVOld.hom D Sc cut s.val t.val) (hf : f ∈ ELVOld.ideal D Sc cut s.val t.val) :
    elvProbeHeightRawEntry D m Sc s t f = 0 := by
  cases n with
  | zero =>
    rcases s with ⟨sv, hsv⟩
    have hs : sv = [] := List.length_eq_zero_iff.mp hsv
    subst sv
    have hf0 : f = 0 := by simpa only [ELVOld.ideal_nil, Submodule.mem_bot] using hf
    rw [hf0, map_zero]
  | succ n =>
    change cyclotomicMk D Sc a n
      (FiniteHomMatrix.single t s (elvProbeScalarHom D m Sc s.val t.val f)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact single_mem_cyclotomicIdeal D Sc a n t s
      (elvProbeAffineSpecialization_ideal D m Sc hf)

/-- Literal specialized matrix entries at every height, including zero. -/
def elvProbeHeightWordEntry {n : ℕ} (s t : Word I n) :
    ELVOld.Old D Sc cut s.val t.val →ₗ[k] heightAlgebra D Sc a n :=
  (ELVOld.ideal D Sc cut s.val t.val).liftQ (elvProbeHeightRawEntry D m Sc s t)
    (by intro f hf; exact elvProbeHeightRawEntry_ideal D m Sc s t f hf)

@[simp] theorem elvProbeHeightWordEntry_mk {n : ℕ} (s t : Word I n)
    (f : ELVOld.hom D Sc cut s.val t.val) :
    elvProbeHeightWordEntry D m Sc s t ((ELVOld.ideal D Sc cut s.val t.val).mkQ f) =
      probeHeightMk D m Sc n
        (FiniteHomMatrix.single t s (elvProbeScalarHom D m Sc s.val t.val f)) := rfl

/-- At positive height this is the already constructed literal cyclotomic entry map. -/
theorem elvProbeHeightWordEntry_succ {n : ℕ} (s t : Word I (n+1)) :
    elvProbeHeightWordEntry D m Sc s t = elvProbeWordEntry D m Sc s t := by
  apply LinearMap.ext
  intro f
  obtain ⟨f, rfl⟩ := (ELVOld.ideal D Sc cut s.val t.val).mkQ_surjective f
  rfl

theorem elvProbeHeightWordEntry_comp {n : ℕ} (s t z : Word I n)
    (f : ELVOld.Old D Sc cut s.val t.val) (g : ELVOld.Old D Sc cut t.val z.val) :
    elvProbeHeightWordEntry D m Sc s z (ELVOld.oldComp D Sc cut s.val t.val z.val f g) =
      elvProbeHeightWordEntry D m Sc t z g * elvProbeHeightWordEntry D m Sc s t f := by
  obtain ⟨f, rfl⟩ := (ELVOld.ideal D Sc cut s.val t.val).mkQ_surjective f
  obtain ⟨g, rfl⟩ := (ELVOld.ideal D Sc cut t.val z.val).mkQ_surjective g
  rw [ELVOld.oldComp_mk, elvProbeHeightWordEntry_mk, elvProbeHeightWordEntry_mk,
    elvProbeHeightWordEntry_mk, ← map_mul, FiniteHomMatrix.single_mul_single]
  exact congrArg (fun h : (pres D Sc).obj (ob D s.val) ⟶ (pres D Sc).obj (ob D z.val) =>
    probeHeightMk D m Sc n (FiniteHomMatrix.single z s h)) (elvProbeScalarHom_comp D m Sc f g)

theorem elvProbeHeightWordEntry_mul_of_ne {n : ℕ} (s t z w : Word I n) (htz : t ≠ z)
    (f : ELVOld.Old D Sc cut t.val s.val) (g : ELVOld.Old D Sc cut w.val z.val) :
    elvProbeHeightWordEntry D m Sc t s f * elvProbeHeightWordEntry D m Sc w z g = 0 := by
  obtain ⟨f, rfl⟩ := (ELVOld.ideal D Sc cut t.val s.val).mkQ_surjective f
  obtain ⟨g, rfl⟩ := (ELVOld.ideal D Sc cut w.val z.val).mkQ_surjective g
  rw [elvProbeHeightWordEntry_mk, elvProbeHeightWordEntry_mk, ← map_mul]
  have hm : (FiniteHomMatrix.single s t (elvProbeScalarHom D m Sc t.val s.val f) : Hn D Sc n) *
      FiniteHomMatrix.single z w (elvProbeScalarHom D m Sc w.val z.val g) = 0 :=
    FiniteHomMatrix.single_mul_single_of_ne s t z w htz _ _
  exact (congrArg (probeHeightMk D m Sc n) hm).trans (map_zero _)

theorem elvProbeHeightWordEntry_id {n : ℕ} (s : Word I n) :
    elvProbeHeightWordEntry D m Sc s s ((ELVOld.ideal D Sc cut s.val s.val).mkQ
      (𝟙 (ELVOld.obj D Sc cut s.val))) = probeHeightMk D m Sc n (Hn.wordIdempotent s) := by
  rw [elvProbeHeightWordEntry_mk]
  exact congrArg (fun h : End ((pres D Sc).obj (ob D s.val)) =>
    probeHeightMk D m Sc n (FiniteHomMatrix.single s s h)) (elvProbeScalarHom_id D m Sc s.val)

theorem probeHeightMk_append (i : I) (n : ℕ) (z : Hn D Sc n) :
    heightAppend D Sc a i n (probeHeightMk D m Sc n z) =
      probeHeightMk D m Sc (n+1) (appendAlgebra D Sc i n z) := by
  cases n <;> rfl

theorem elvProbeHeightWordEntry_append {n : ℕ} (i : I) (s t : Word I n)
    (f : ELVOld.Old D Sc cut s.val t.val) :
    heightAppend D Sc a i n (elvProbeHeightWordEntry D m Sc s t f) =
      elvProbeHeightWordEntry D m Sc (appendWord i s) (appendWord i t)
        (elvProbeOldRightContext D m Sc [i] s.val t.val f) := by
  obtain ⟨f, rfl⟩ := (ELVOld.ideal D Sc cut s.val t.val).mkQ_surjective f
  change heightAppend D Sc a i n
      (probeHeightMk D m Sc n (FiniteHomMatrix.single t s (elvProbeScalarHom D m Sc s.val t.val f))) =
    probeHeightMk D m Sc (n+1) (FiniteHomMatrix.single (appendWord i t) (appendWord i s)
      (elvProbeScalarHom D m Sc (s.val++[i]) (t.val++[i])
        (ELVOld.rightContext D Sc cut [i] s.val t.val f)))
  rw [probeHeightMk_append]
  change probeHeightMk D m Sc (n+1)
    (appendLinear D Sc i n (FiniteHomMatrix.single t s (elvProbeScalarHom D m Sc s.val t.val f))) = _
  rw [appendLinear_single]
  have hc : elvProbeScalarHom D m Sc (s.val++[i]) (t.val++[i])
        (ELVOld.rightContext D Sc cut [i] s.val t.val f) =
      ELVOld.affineRightContext D Sc [i] s.val t.val (elvProbeScalarHom D m Sc s.val t.val f) :=
    elvAffineScalarSpecialization_rightContext D Sc cut (probeScalarValues D m)
      (probeScalarValues_vanish D m) [i] s.val t.val f
  exact congrArg (fun h : (pres D Sc).obj (ob D (s.val++[i])) ⟶
      (pres D Sc).obj (ob D (t.val++[i])) =>
    probeHeightMk D m Sc (n+1) (FiniteHomMatrix.single (appendWord i t) (appendWord i s) h)) hc.symm

/-- A content permutation viewed in the existing fixed-height word type. -/
def probeContentWord (ν : List I) (v : ELVOld.ContentWords ν) : Word I ν.length :=
  ⟨v.val, v.property.length_eq⟩

omit [Fintype I] in
theorem probeContentWord_injective (ν : List I) : Function.Injective (probeContentWord ν) := by
  intro v w h
  apply Subtype.ext
  exact congrArg (fun z : Word I ν.length => z.val) h

/-- Specialization on the canonical matrix-entry Hom type. -/
def elvProbeContentEntry (ν : List I) (p : ELVOld.ContentWords ν × ELVOld.ContentWords ν) :
    (ELVOld.contentObject D Sc cut ν p.2 ⟶ ELVOld.contentObject D Sc cut ν p.1) →ₗ[k]
      heightAlgebra D Sc a ν.length where
  toFun f := elvProbeHeightWordEntry D m Sc (probeContentWord ν p.2) (probeContentWord ν p.1) f
  map_add' f g := map_add _ f g
  map_smul' c f := map_smul _ c f

/-- The finite content-matrix map, assembled from the literal height entries. -/
def elvProbeContentLinear (ν : List I) :
    ELVOld.ContentRing D Sc cut ν →ₗ[k] heightAlgebra D Sc a ν.length :=
  DFinsupp.lsum k (elvProbeContentEntry D m Sc ν)

@[simp] theorem elvProbeContentLinear_single (ν : List I) (v w : ELVOld.ContentWords ν)
    (f : ELVOld.contentObject D Sc cut ν w ⟶ ELVOld.contentObject D Sc cut ν v) :
    elvProbeContentLinear D m Sc ν (FiniteHomMatrix.single v w f) =
      elvProbeContentEntry D m Sc ν (v,w) f := by
  let : DecidableEq (ELVOld.ContentWords ν) := Classical.decEq _
  exact DFinsupp.lsum_single (S := k) (elvProbeContentEntry D m Sc ν) (v,w) f

private theorem elvProbeContentLinear_single_product (ν : List I) (s t u v : ELVOld.ContentWords ν)
    (f : ELVOld.contentObject D Sc cut ν t ⟶ ELVOld.contentObject D Sc cut ν s)
    (g : ELVOld.contentObject D Sc cut ν v ⟶ ELVOld.contentObject D Sc cut ν u) :
    elvProbeContentLinear D m Sc ν (FiniteHomMatrix.single s t f * FiniteHomMatrix.single u v g) =
      elvProbeContentLinear D m Sc ν (FiniteHomMatrix.single s t f) *
        elvProbeContentLinear D m Sc ν (FiniteHomMatrix.single u v g) := by
  by_cases h : t = u
  · subst u
    rw [FiniteHomMatrix.single_mul_single, elvProbeContentLinear_single,
      elvProbeContentLinear_single, elvProbeContentLinear_single]
    exact elvProbeHeightWordEntry_comp D m Sc (probeContentWord ν v)
      (probeContentWord ν t) (probeContentWord ν s) g f
  · rw [FiniteHomMatrix.single_mul_single_of_ne s t u v h, map_zero,
      elvProbeContentLinear_single, elvProbeContentLinear_single]
    have hn : probeContentWord ν t ≠ probeContentWord ν u :=
      fun he => h (probeContentWord_injective ν he)
    exact (elvProbeHeightWordEntry_mul_of_ne D m Sc (probeContentWord ν s) (probeContentWord ν t)
      (probeContentWord ν u) (probeContentWord ν v) hn f g).symm

theorem elvProbeContentLinear_mul (ν : List I) (x y : ELVOld.ContentRing D Sc cut ν) :
    elvProbeContentLinear D m Sc ν (x*y) =
      elvProbeContentLinear D m Sc ν x * elvProbeContentLinear D m Sc ν y := by
  induction x using FiniteHomMatrix.induction with
  | hz => simp only [zero_mul, map_zero]
  | ha x z hx hz => simp only [add_mul, map_add, hx, hz]
  | hs s t f =>
    induction y using FiniteHomMatrix.induction with
    | hz => simp only [mul_zero, map_zero]
    | ha y z hy hz => simp only [mul_add, map_add, hy, hz]
    | hs u v g => exact elvProbeContentLinear_single_product D m Sc ν s t u v f g

/-- The untruncated content-ring specialization before restriction to its unit corner. -/
def elvProbeContentNonUnital (ν : List I) :
    ELVOld.ContentRing D Sc cut ν →ₙₐ[k] heightAlgebra D Sc a ν.length where
  toFun := elvProbeContentLinear D m Sc ν
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := elvProbeContentLinear_mul D m Sc ν

/-- The literal content idempotent in the existing height algebra. -/
def probeHeightContentIdempotent (ν : List I) : heightAlgebra D Sc a ν.length :=
  probeHeightMk D m Sc ν.length (contentIdempotent D Sc ν.length (ν : Multiset I))

theorem probeHeightContentIdempotent_idem (ν : List I) :
    IsIdempotentElem (probeHeightContentIdempotent D m Sc ν) := by
  change probeHeightMk D m Sc ν.length _ * probeHeightMk D m Sc ν.length _ =
    probeHeightMk D m Sc ν.length _
  rw [← map_mul, contentIdempotent_sq]

/-- The actual content corner, uniformly including the vacuum height. -/
abbrev ProbeHeightContentCorner (ν : List I) :=
  (probeHeightContentIdempotent_idem D m Sc ν).Corner

omit [Fintype I] in
private def probeContentWordEquiv (ν : List I) :
    ELVOld.ContentWords ν ≃ {w : Word I ν.length // wordContent w = (ν : Multiset I)} where
  toFun v := ⟨probeContentWord ν v, Multiset.coe_eq_coe.mpr v.property⟩
  invFun w := ⟨w.val.val, Multiset.coe_eq_coe.mp w.property⟩
  left_inv _v := Subtype.ext rfl
  right_inv _w := Subtype.ext (Subtype.ext rfl)

theorem elvProbeContentNonUnital_one (ν : List I) :
    elvProbeContentNonUnital D m Sc ν 1 = probeHeightContentIdempotent D m Sc ν := by
  change elvProbeContentLinear D m Sc ν (FiniteHomMatrix.localUnit Finset.univ) =
    probeHeightMk D m Sc ν.length (contentIdempotent D Sc ν.length (ν : Multiset I))
  rw [FiniteHomMatrix.localUnit, map_sum]
  simp only [FiniteHomMatrix.idem, elvProbeContentLinear_single]
  unfold contentIdempotent FiniteHomMatrix.localUnit
  rw [map_sum, Finset.sum_subtype (p := fun w : Word I ν.length => wordContent w = (ν : Multiset I))
    _ (by intro w; simp)]
  exact Fintype.sum_equiv (probeContentWordEquiv ν) _ _ (fun v => elvProbeHeightWordEntry_id D m Sc (probeContentWord ν v))

@[simp] theorem probeHeightContentIdempotent_nil :
    probeHeightContentIdempotent D m Sc [] = (1 : heightAlgebra D Sc a 0) := by
  change contentIdempotent D Sc 0 0 = (1 : Hn D Sc 0)
  change FiniteHomMatrix.localUnit (Finset.univ.filter (fun w : Word I 0 => wordContent w = 0)) =
    FiniteHomMatrix.localUnit Finset.univ
  congr 1

/-- At positive height the corner is exactly the existing cyclotomic content corner. -/
theorem probeHeightContentCorner_cons (i : I) (ν : List I) :
    ProbeHeightContentCorner D m Sc (i::ν) =
      CyclotomicContentCorner D Sc a ν.length ((i::ν : List I) : Multiset I) := rfl


private def probeHeightContentSubmodule (ν : List I) : Submodule k (heightAlgebra D Sc a ν.length) where
  carrier := (Subsemigroup.corner (probeHeightContentIdempotent D m Sc ν) : Set _)
  zero_mem' := (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mpr
    ⟨mul_zero _, zero_mul _⟩
  add_mem' := by
    intro x y hx hy
    have hx := (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mp hx
    have hy := (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mp hy
    apply (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mpr
    constructor
    · rw [mul_add, hx.1, hy.1]
    · rw [add_mul, hx.2, hy.2]
  smul_mem' := by
    intro c x hx
    have hx := (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mp hx
    apply (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mpr
    constructor
    · rw [mul_smul_comm, hx.1]
    · rw [smul_mul_assoc, hx.2]

instance probeHeightContentCornerModule (ν : List I) :
    Module k (ProbeHeightContentCorner D m Sc ν) :=
  inferInstanceAs (Module k (probeHeightContentSubmodule D m Sc ν))

instance probeHeightContentCornerAlgebra (ν : List I) :
    Algebra k (ProbeHeightContentCorner D m Sc ν) :=
  Algebra.ofModule
    (fun c x y => Subtype.ext (smul_mul_assoc c x.val y.val))
    (fun c x y => by apply Subtype.ext; change x.val * (c • y.val) = _; rw [mul_smul_comm]; rfl)

/-- The untruncated ELV old content ring maps to the literal ordinary probe content corner. -/
def elvProbeContentSpecialization (ν : List I) :
    ELVOld.ContentRing D Sc cut ν →ₐ[k] ProbeHeightContentCorner D m Sc ν where
  toFun x := ⟨elvProbeContentNonUnital D m Sc ν x, by
    apply (Subsemigroup.mem_corner_iff (probeHeightContentIdempotent_idem D m Sc ν)).mpr
    constructor
    · rw [← elvProbeContentNonUnital_one, ← map_mul, one_mul]
    · rw [← elvProbeContentNonUnital_one, ← map_mul, mul_one]⟩
  map_zero' := Subtype.ext (map_zero (elvProbeContentNonUnital D m Sc ν))
  map_one' := Subtype.ext (elvProbeContentNonUnital_one D m Sc ν)
  map_add' x y := Subtype.ext (map_add (elvProbeContentNonUnital D m Sc ν) x y)
  map_mul' x y := Subtype.ext (map_mul (elvProbeContentNonUnital D m Sc ν) x y)
  commutes' c := by
    apply Subtype.ext
    change elvProbeContentNonUnital D m Sc ν
        (algebraMap k (ELVOld.ContentRing D Sc cut ν) c) =
      (algebraMap k (ProbeHeightContentCorner D m Sc ν) c).val
    rw [Algebra.algebraMap_eq_smul_one, map_smul, elvProbeContentNonUnital_one]
    rw [Algebra.algebraMap_eq_smul_one]
    rfl

@[simp] theorem elvProbeContentSpecialization_val (ν : List I) (x : ELVOld.ContentRing D Sc cut ν) :
    (elvProbeContentSpecialization D m Sc ν x).val = elvProbeContentNonUnital D m Sc ν x := rfl

/-- The algebra map retains the actual rectangular matrix-entry specialization. -/
theorem elvProbeContentSpecialization_single (ν : List I) (v w : ELVOld.ContentWords ν)
    (f : ELVOld.contentObject D Sc cut ν w ⟶ ELVOld.contentObject D Sc cut ν v) :
    (elvProbeContentSpecialization D m Sc ν (FiniteHomMatrix.single v w f)).val =
      elvProbeContentEntry D m Sc ν (v,w) f := by
  rw [elvProbeContentSpecialization_val]
  exact elvProbeContentLinear_single D m Sc ν v w f

/-- An appended word belongs to the enlarged content frame. -/
def probeContentAppendWord (i : I) (ν : List I) (v : ELVOld.ContentWords ν) :
    ELVOld.ContentWords (i::ν) :=
  ⟨v.val++[i], (v.property.append_right [i]).trans (List.perm_append_comm : (ν++[i]).Perm ([i]++ν))⟩

/-- On every matrix generator the algebra specialization commutes with the existing height append. -/
theorem elvProbeContentSpecialization_append_single (i : I) (ν : List I)
    (v w : ELVOld.ContentWords ν)
    (f : ELVOld.contentObject D Sc cut ν w ⟶ ELVOld.contentObject D Sc cut ν v) :
    heightAppend D Sc a i ν.length
        (elvProbeContentSpecialization D m Sc ν (FiniteHomMatrix.single v w f)).val =
      (elvProbeContentSpecialization D m Sc (i::ν)
        (FiniteHomMatrix.single (probeContentAppendWord i ν v) (probeContentAppendWord i ν w)
          (elvProbeOldRightContext D m Sc [i] w.val v.val f))).val := by
  rw [elvProbeContentSpecialization_single, elvProbeContentSpecialization_single]
  exact elvProbeHeightWordEntry_append D m Sc i (probeContentWord ν w) (probeContentWord ν v) f

/-- The vacuum corner unit is the genuine unit of the original empty-word height algebra. -/
theorem elvProbeContentSpecialization_nil_one :
    (elvProbeContentSpecialization D m Sc [] 1).val = (1 : heightAlgebra D Sc a 0) := by
  rw [elvProbeContentSpecialization_val, elvProbeContentNonUnital_one, probeHeightContentIdempotent_nil]

end OddMath.QuiverHecke
