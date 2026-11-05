import OddMath.QuiverHecke.CyclotomicAction.ELVProbeSpecialization
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModule
import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicSpan
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight
import OddMath.QuiverHecke.CyclotomicAction.AppendContentCorner

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

theorem elvProbeHeightWordEntry_id {n : ℕ} (s : Word I n) :
    elvProbeHeightWordEntry D m Sc s s ((ELVOld.ideal D Sc cut s.val s.val).mkQ
      (𝟙 (ELVOld.obj D Sc cut s.val))) = probeHeightMk D m Sc n (Hn.wordIdempotent s) := by
  rw [elvProbeHeightWordEntry_mk]
  exact congrArg (fun h : End ((pres D Sc).obj (ob D s.val)) =>
    probeHeightMk D m Sc n (FiniteHomMatrix.single s s h)) (elvProbeScalarHom_id D m Sc s.val)

/-- A content permutation viewed in the existing fixed-height word type. -/
def probeContentWord (ν : List I) (v : ELVOld.ContentWords ν) : Word I ν.length :=
  ⟨v.val, v.property.length_eq⟩

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

end OddMath.QuiverHecke
