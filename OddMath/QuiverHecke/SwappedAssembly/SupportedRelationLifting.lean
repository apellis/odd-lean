import OddMath.QuiverHecke.SwappedAssembly.SupportedWhiskerReduction
import OddMath.QuiverHecke.SwappedAssembly.SupportedGeneratorEntries

/-! # Whiskering relations on the supported Hom inputs

The exact-support attachment F4/(A1) of `SwappedActionAssembly.md`:
the native path functors preserve the replete supported inputs. A local
defining relation on these objects therefore gives its exact native
layer-representation relation for supported rightmost inputs.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ProbeReservoir
universe u
local instance supportedRelationHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

/-- The prescribed replete formal-content support as a property of the raw Hom input. -/
def retainedInput (t : Sector I) : ObjectProperty ((P).H t) :=
  ContentHomSupport.Supported D Sc' m cutoff bound
    (probeBlock D ΛP t) (reservoirBlock D ΛR t)

/-- Every native summand path preserves this exact input property. -/
theorem retainedInput_path {w : List (Col I X)} {s t : Sector I}
    (p : SPath w s t) (Z : (P).H t)
    (hZ : retainedInput D Sc m cutoff bound ΛP ΛR hP hR t Z) :
    retainedInput D Sc m cutoff bound ΛP ΛR hP hR s (((P).pathFunctor p).obj Z) := by
  let W : H D Sc' m cutoff bound ΛP ΛR t := ⟨Z, hZ⟩
  have h := ((pathFunctor D Sc' m cutoff bound ΛP ΛR p).obj W).property
  rw [factor_path_obj D Sc m cutoff bound ΛP ΛR hP hR p W] at h
  exact h

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
