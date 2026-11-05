import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendSpecialization
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport

/-! # The nonzero empty vector of the regular probe

The probe vacuum T₀ in `SwappedActionAssembly.md`, F2, is the genuine
height-zero regular module. Its empty word-idempotent vector is nonzero
by the original affine empty-word PBW coordinate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

variable [Fintype I] (m : I → ℕ)

/-- The original empty object in the old scalar-probe source category. -/
def probeOldVacuumObject : ELVOld.OldContentCategory D Sc (probeCutoff D m) [] :=
  ⟨⟨[]⟩, List.Perm.refl _⟩

/-- The literal regular height-zero probe, with its existing old Hom action. -/
abbrev probeOldVacuumRegular :=
  probeOldModule D m Sc [] (SuperBimodule.regular
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) 0))

/-- The actual empty word idempotent, as a vector of its fixed submodule. -/
def probeOldVacuumVector :
    (probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m) :=
  ⟨probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m), by
    change probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m) *
      probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m) =
        probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m)
    change Hn.wordIdempotent (vacuumWord (I := I)) * Hn.wordIdempotent (vacuumWord (I := I)) =
      Hn.wordIdempotent (vacuumWord (I := I))
    exact Hn.wordIdempotent_sq _⟩

end OddMath.QuiverHecke
