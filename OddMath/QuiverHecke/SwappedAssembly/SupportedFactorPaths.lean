import OddMath.QuiverHecke.SwappedAssembly.SupportedPaths
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir

/-! # The chosen factor paths on exact-support sectors

The attachment of F1–F2 to F4/(A1)–(A3) in `SwappedActionAssembly.md`.
The chosen OLD probe and ELV reservoir give exactly the already constructed
native steps, including their asymmetric parity shifts. Thus their whole
path functors restrict through the computed full inclusions, without a
new support-preservation or comparison hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance piSCatHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

/-- Each of the chosen factor's four steps is the literal native supported-sector step. -/
theorem factor_step (l : Letter I) (side : Bool) (t : Sector I) (hv : StepValid l side t) :
    (P).step l side t hv = (nativeStep D Sc' m cutoff bound ΛP ΛR l side t hv).toFunctor := by
  obtain ⟨up, i⟩ := l
  cases up <;> cases side <;> rfl

/-- The chosen factor and native path functors agree on objects and all maps. -/
theorem factor_pathFunctor {w : List (Col I X)} {s t : Sector I} (p : SPath w s t) :
    (P).pathFunctor p = (nativePathFunctor D Sc' m cutoff bound ΛP ΛR p).toFunctor := by
  induction p with
  | nil t => rfl
  | cons c side s hv p ih =>
    change (P).pathFunctor p ⋙ (P).step c.l side s hv = _
    rw [ih, factor_step]
    rfl

/-- Inclusion identifies a supported path with the whole chosen factor path. -/
theorem factor_pathFunctor_inclusion {w : List (Col I X)} {s t : Sector I}
    (p : SPath w s t) :
    (pathFunctor D Sc' m cutoff bound ΛP ΛR p).toFunctor ⋙
      inclusion D Sc' m cutoff bound ΛP ΛR s =
    inclusion D Sc' m cutoff bound ΛP ΛR t ⋙ (P).pathFunctor p := by
  rw [factor_pathFunctor]
  exact pathFunctor_inclusion D Sc' m cutoff bound ΛP ΛR p

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
