import OddMath.QuiverHecke.SwappedAssembly.SupportedSteps

/-! # Supported path functors and their literal native inclusions

The path attachment needed for restricting the generator matrices of
`SwappedActionAssembly.md`, F4/(A1). Every finite path retains its actual
formal endpoints and all native step shifts. The full inclusion commutes
with the whole functor on objects and arbitrary homogeneous maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)

/-- Compose the specified native steps along the literal formal path. -/
def nativePathFunctor : {w : List (Col I X)} → {s t : Sector I} → SPath w s t →
    Superfunctor k (Ambient D Sc m cutoff bound ΛP ΛR t)
      (Ambient D Sc m cutoff bound ΛP ΛR s)
  | _, _, _, .nil _ => Superfunctor.id k _
  | _, _, _, .cons c side s hv p =>
    (nativePathFunctor p).comp (nativeStep D Sc m cutoff bound ΛP ΛR c.l side s hv)

/-- The same path in the exact-support categories, with every native arrow retained. -/
def pathFunctor : {w : List (Col I X)} → {s t : Sector I} → SPath w s t →
    Superfunctor k (H D Sc m cutoff bound ΛP ΛR t) (H D Sc m cutoff bound ΛP ΛR s)
  | _, _, _, .nil _ => Superfunctor.id k _
  | _, _, _, .cons c side s hv p =>
    (pathFunctor p).comp (step D Sc m cutoff bound ΛP ΛR c.l side s hv)

/-- The full inclusion recovers the entire native word functor, on every map. -/
theorem pathFunctor_inclusion {w : List (Col I X)} {s t : Sector I} (p : SPath w s t) :
    (pathFunctor D Sc m cutoff bound ΛP ΛR p).toFunctor ⋙ inclusion D Sc m cutoff bound ΛP ΛR s =
      inclusion D Sc m cutoff bound ΛP ΛR t ⋙
        (nativePathFunctor D Sc m cutoff bound ΛP ΛR p).toFunctor := by
  induction p with
  | nil t => rfl
  | cons c side s hv p ih =>
    change (pathFunctor D Sc m cutoff bound ΛP ΛR p).toFunctor ⋙
      ((step D Sc m cutoff bound ΛP ΛR c.l side s hv).toFunctor ⋙
        inclusion D Sc m cutoff bound ΛP ΛR s) = _
    rw [step_inclusion]
    change ((pathFunctor D Sc m cutoff bound ΛP ΛR p).toFunctor ⋙
      inclusion D Sc m cutoff bound ΛP ΛR _) ⋙
      (nativeStep D Sc m cutoff bound ΛP ΛR c.l side s hv).toFunctor = _
    rw [ih]
    rfl

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
