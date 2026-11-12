import OddMath.QuiverHecke.SwappedAssembly.SupportedFactorPaths
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Generators

/-! # Chosen generator entries on supported sectors

The matrix-entry attachment of F4/(A1) to the chosen OLD/ELV factor
families in `SwappedActionAssembly.md`. Every `ProbeReservoir.GenImage`
restricts at its original formal endpoints. The path comparison is the
computed comparison of the chosen factor fields, with no supplied
support premise. Supernatural entries retain their generator parity.
This transport does not assert the remaining central inverse or the
complete presentation relations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance generatorHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

/-- The included path object is exactly the chosen factor path object. -/
theorem factor_path_obj {w : List (Col I X)} {s t : Sector I} (p : SPath w s t)
    (Z : H D Sc' m cutoff bound ΛP ΛR t) :
    ((pathFunctor D Sc' m cutoff bound ΛP ΛR p).obj Z).obj =
      ((P).pathFunctor p).obj Z.obj :=
  congrArg (fun F => F.obj Z) (factor_pathFunctor_inclusion D Sc m cutoff bound ΛP ΛR hP hR p)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
