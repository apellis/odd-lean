import OddMath.QuiverHecke.HalfTurn.QuotientEquivalence

/-! # Bounded detection in the actual reversed first-boundary quotient

SwappedVacuumCoordinates §§5–6. Compose the actual half-turn with the
first-boundary quotient at the twisted parameters. The proved kernel
identity and transformed-ideal weight bound give bounded injectivity,
including the literal reservoir schedule and optional heavy coefficients.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The actual reversed/twisted first-boundary quotient coordinate map. -/
def halfTurnBoundaryClass (cutoff : I → ℕ) (T : Set (SKM.SYM D k)) (s t : List I) :=
  (ELVRelationSpan D (parameterTwist D Sc) cutoff t.reverse s.reverse ⊔
    CoefficientGeneratorSpan D (parameterTwist D Sc) T t.reverse s.reverse).mkQ ∘ₗ
    htCoef D Sc s t

/-- The kernel is the transformed last-boundary ideal, with the same full
homogeneous coefficient generators. It is proved, rather than supplied as
an observation hypothesis. -/
theorem halfTurnBoundaryClass_ker (cutoff : I → ℕ) (T : Set (SKM.SYM D k))
    (hT : ∀ a ∈ T, ∃ p, CoefParity D p a) (s t : List I) :
    LinearMap.ker (halfTurnBoundaryClass D Sc cutoff T s t) =
      TransformedIdeal D Sc cutoff T s t := by
  rw [halfTurnBoundaryClass, LinearMap.ker_comp, Submodule.ker_mkQ]
  exact comap_htCoef_elvRelationSpan_sup D Sc cutoff T hT s t

/-- Bounded source coefficient/affine windows are detected by the actual
reversed first-boundary quotient, with no assumed evaluation kernel. -/
theorem halfTurnBoundaryClass_injective_on_extendedAtMost
    {cutoff : I → ℕ} {T : Set (SKM.SYM D k)} {s t : List I} {d N : ℕ}
    (hTparity : ∀ a ∈ T, ∃ p, CoefParity D p a)
    (hN : ∀ i, N ≤ cutoff i)
    (hTweight : ∀ a ∈ T, a ∈ SKM.SYM.CoefficientAtLeast D k N)
    (hd : d + 2 * s.length.choose 2 < N) :
    Function.Injective (fun x : ExtendedAtMost D Sc s t d =>
      halfTurnBoundaryClass D Sc cutoff T s t x.val) := by
  intro x y hxy
  apply transformedIdeal_quotient_injective_on_extendedAtMost D Sc hN hTweight hd
  apply (halfTurnQuotientEquiv D Sc cutoff T hTparity s t).injective
  change halfTurnBoundaryClass D Sc cutoff T s t x.val =
    halfTurnBoundaryClass D Sc cutoff T s t y.val
  exact hxy

/-- The same detection statement for the prescribed reservoir schedule. -/
theorem halfTurnBoundaryClass_reservoir_injective (μ : X) (s t : List I) (d : ℕ)
    {T : Set (SKM.SYM D k)} (hTparity : ∀ a ∈ T, ∃ p, CoefParity D p a)
    (hTweight : ∀ a ∈ T, a ∈ SKM.SYM.CoefficientAtLeast D k (vacuumCutoff s d)) :
    Function.Injective (fun x : ExtendedAtMost D Sc s t d =>
      halfTurnBoundaryClass D Sc (reservoirLevel D μ s d) T s t x.val) :=
  halfTurnBoundaryClass_injective_on_extendedAtMost D Sc hTparity
    (vacuumCutoff_le_reservoirLevel D μ s d) hTweight (by simp [vacuumCutoff])

end OddMath.QuiverHecke
