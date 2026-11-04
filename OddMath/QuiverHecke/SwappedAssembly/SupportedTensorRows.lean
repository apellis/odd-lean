import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import OddMath.QuiverHecke.SwappedAssembly.SupportedPresentation
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerEntries

/-! # The actual tensor-vacuum matrix module and its fixed source row

SwappedVacuumCoordinates §3: reduce the specified full matrix module,
with its zero-padded whole-sector families, to its actual source-word Hom.
The existing full-inclusion chart is applied before normalizing the two
chosen family entries. Off-row arrows vanish as whole functor maps,
without regular-input faithfulness or quotient-coordinate choices.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorRowsHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "Gs" => tensorSourceFamily D Sc m cutoff ΛP ΛR L s
local notation "Ys" => tensorTargetFamily D Sc m cutoff ΛP ΛR L
local notation "S" => (0,tensorSourceContent D ΛP ΛR s)
local notation "V" => ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)
local notation "G" => ObjectProperty.FullSubcategory.obj (tensorSourceObject D Sc m cutoff ΛP ΛR L s)
variable {a : Obj (SKM.sig D)}
  (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = a.endR)
  (p : SPath a.word S (0,0))

/-- Full inclusion followed by normalization of the specified source and vacuum entries. -/
def tensorRowChart :=
  (entryEquiv D Sc m cutoff N ΛP ΛR hP hR p (Gs S) (Ys (0,0))).trans
    (Linear.homCongr k
      (eqToIso (congrArg (fun Z : H D Sc' m cutoff N ΛP ΛR S => Z.obj)
        (tensorSourceFamily_source D Sc m cutoff ΛP ΛR L s)))
      (((P).pathFunctor p).mapIso (eqToIso (congrArg
        (fun Z : H D Sc' m cutoff N ΛP ΛR (0,0) => Z.obj)
          (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L)))))

/-- Observe the actual full supported matrix at its fixed source-word row. -/
def tensorMatrixEntry : matrixModule D Sc m cutoff N ΛP ΛR Gs Ys a →ₗ[k]
    (G ⟶ ((P).pathFunctor p).obj V) where
  toFun x := tensorRowChart D Sc m cutoff ΛP ΛR L hP hR s p (x S ⟨(0,0),hEnd⟩ p)
  map_add' x y := (tensorRowChart D Sc m cutoff ΛP ΛR L hP hR s p).map_add _ _
  map_smul' r x := (tensorRowChart D Sc m cutoff ΛP ΛR L hP hR s p).map_smul r _

/-- Whole-functor zeros in the other sectors make the retained row determine the entire matrix. -/
theorem tensorMatrixEntry_injective (hup : ∀ c ∈ a.word, c.l.1 = true) :
    Function.Injective (tensorMatrixEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p) := by
  intro x y h
  funext sl ⟨sr,hweight⟩ q
  classical
  by_cases hsl : sl = S
  · subst sl
    by_cases hsr : sr = (0,0)
    · subst sr
      have hq : q = p := (SPath.subsingleton_of_upward_probe_zero hup rfl).elim _ _
      subst q
      exact (tensorRowChart D Sc m cutoff ΛP ΛR L hP hR s p).injective h
    · have hz := (pathFunctor D Sc' m cutoff N ΛP ΛR q).toFunctor.map_isZero
        (tensorTargetFamily_isZero D Sc m cutoff ΛP ΛR L sr hsr)
      exact hz.eq_of_tgt _ _
  · exact (tensorSourceFamily_isZero D Sc m cutoff ΛP ΛR L s sl hsl).eq_of_src _ _

/-- Insert the genuine whole source-Hom arrow and zero in every other formal sector. -/
def tensorMatrixOfEntry (hup : ∀ c ∈ a.word, c.l.1 = true)
    (f : G ⟶ ((P).pathFunctor p).obj V) :
    matrixModule D Sc m cutoff N ΛP ΛR Gs Ys a := by
  classical
  intro sl sr q
  by_cases hsl : sl = S
  · subst sl
    by_cases hsr : sr.1 = (0,0)
    · rcases sr with ⟨sr,hweight⟩
      dsimp only at hsr
      subst sr
      have hq : q = p := (SPath.subsingleton_of_upward_probe_zero hup rfl).elim _ _
      subst q
      exact (tensorRowChart D Sc m cutoff ΛP ΛR L hP hR s p).symm f
    · exact 0
  · exact 0

/-- Observation recovers the inserted actual source-Hom arrow. -/
theorem tensorMatrixEntry_ofEntry (hup : ∀ c ∈ a.word, c.l.1 = true)
    (f : G ⟶ ((P).pathFunctor p).obj V) :
    tensorMatrixEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p
      (tensorMatrixOfEntry D Sc m cutoff ΛP ΛR L hP hR s p hup f) = f := by
  classical
  simp [tensorMatrixEntry,tensorMatrixOfEntry]

/-- The actual full supported matrix module is its genuine fixed-source word-Hom row. -/
def tensorMatrixRowEquiv (hup : ∀ c ∈ a.word, c.l.1 = true) :
    matrixModule D Sc m cutoff N ΛP ΛR Gs Ys a ≃ₗ[k]
      (G ⟶ ((P).pathFunctor p).obj V) :=
  LinearEquiv.ofBijective (tensorMatrixEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p)
    ⟨tensorMatrixEntry_injective D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup,
      fun f => ⟨tensorMatrixOfEntry D Sc m cutoff ΛP ΛR L hP hR s p hup f,
        tensorMatrixEntry_ofEntry D Sc m cutoff ΛP ΛR L hP hR s hEnd p hup f⟩⟩

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
