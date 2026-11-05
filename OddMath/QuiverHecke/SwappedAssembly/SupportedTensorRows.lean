import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import OddMath.QuiverHecke.SwappedAssembly.SupportedPresentation
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerEntries

/-! # Actual fixed-source rows of the supported tensor matrix

SwappedVacuumCoordinates §3: whole-functor zero padding and uniqueness
of the upward reservoir path reduce the specified full matrix module to
its genuine source-word Hom. The generic row calculation is performed
with abstract sector families, then specialized to the constructed
families; no regular-input faithfulness or quotient coordinates are used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorRowsHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
namespace MatrixSourceRow
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (Gs Ys : ∀ t, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
  (sl : Sector I) {a : Obj (SKM.sig D)}
  (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = a.endR)
  (p : SPath a.word sl (0,0))
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "Sc'" => parameterTwist D Sc

/-- Literal matrix projection followed by the existing full-inclusion entry chart. -/
def projection : matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys a →ₗ[k]
    ((Gs sl).obj ⟶ ((P).pathFunctor p).obj (Ys (0,0)).obj) where
  toFun x := entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs sl) (Ys (0,0))
    (x sl ⟨(0,0),hEnd⟩ p)
  map_add' x y := (entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs sl) (Ys (0,0))).map_add (x sl ⟨(0,0),hEnd⟩ p) (y sl ⟨(0,0),hEnd⟩ p)
  map_smul' r x := (entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs sl) (Ys (0,0))).map_smul r (x sl ⟨(0,0),hEnd⟩ p)

/-- Intermediate row calculation: its zero-object premises are supplied by the constructed sector families. -/
theorem projection_injective (hup : ∀ c ∈ a.word, c.l.1 = true)
    (hGs : ∀ t, t ≠ sl → Limits.IsZero (Gs t))
    (hYs : ∀ t, t ≠ (0,0) → Limits.IsZero (Ys t)) :
    Function.Injective (projection D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl hEnd p) := by
  intro x y h
  funext t ⟨sr,hweight⟩ q
  classical
  by_cases ht : t = sl
  · subst t
    by_cases hsr : sr = (0,0)
    · subst sr
      have hq : q = p := (SPath.subsingleton_of_upward_probe_zero hup rfl).elim _ _
      subst q
      exact (entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs sl) (Ys (0,0))).injective h
    · have hz := (pathFunctor D Sc' m cutoff bound ΛP ΛR q).toFunctor.map_isZero (hYs sr hsr)
      exact hz.eq_of_tgt _ _
  · exact (hGs t ht).eq_of_src _ _

/-- Insert the original whole Hom arrow in its unique upward source-row entry. -/
def insertion (hup : ∀ c ∈ a.word, c.l.1 = true)
    (f : (Gs sl).obj ⟶ ((P).pathFunctor p).obj (Ys (0,0)).obj) :
    matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys a := by
  classical
  intro t sr q
  by_cases ht : t = sl
  · subst t
    by_cases hsr : sr.1 = (0,0)
    · rcases sr with ⟨sr,hweight⟩
      dsimp only at hsr
      subst sr
      have hq : q = p := (SPath.subsingleton_of_upward_probe_zero hup rfl).elim _ _
      subst q
      exact (entryEquiv D Sc m cutoff bound ΛP ΛR hP hR p (Gs sl) (Ys (0,0))).symm f
    · exact 0
  · exact 0

theorem projection_insertion (hup : ∀ c ∈ a.word, c.l.1 = true)
    (f : (Gs sl).obj ⟶ ((P).pathFunctor p).obj (Ys (0,0)).obj) :
    projection D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl hEnd p
      (insertion D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl p hup f) = f := by
  classical
  simp [projection,insertion]

/-- Intermediate whole-matrix row equivalence, using only its stated zero padding and path condition. -/
def equiv (hup : ∀ c ∈ a.word, c.l.1 = true)
    (hGs : ∀ t, t ≠ sl → Limits.IsZero (Gs t))
    (hYs : ∀ t, t ≠ (0,0) → Limits.IsZero (Ys t)) :
    matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys a ≃ₗ[k]
      ((Gs sl).obj ⟶ ((P).pathFunctor p).obj (Ys (0,0)).obj) :=
  LinearEquiv.ofBijective (projection D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl hEnd p)
    ⟨projection_injective D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl hEnd p hup hGs hYs,
      fun f => ⟨insertion D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl p hup f,
        projection_insertion D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl hEnd p hup f⟩⟩
end MatrixSourceRow

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
  {a : Obj (SKM.sig D)}
  (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = a.endR)
  (p : SPath a.word (0,tensorSourceContent D ΛP ΛR s) (0,0))
  (hup : ∀ c ∈ a.word, c.l.1 = true)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
