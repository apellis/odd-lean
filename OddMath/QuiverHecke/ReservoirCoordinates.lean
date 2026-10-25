/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirVacuumDetection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Bounded connected reservoir coordinates

The bounded-coordinate step corresponding to
`Categorification/KLR/Unfurling/Triangular.lean` and
`Categorification/KLR/Unfurling/GenericVacuumWordCoordinates.lean`.
Here the connected super PBW bound supplies injectivity before a vector-space
splitting constructs coordinates. All colourwise exterior products remain in
the same coefficient-extended Hom. No factorization into rank-one actions or
automorphism of a finite ELV quotient is used.

These are coordinates on the connected regular quotient. Identification of
that quotient with a fused vacuum module is a separate categorical obligation.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [Field k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (cutoff : I → ℕ) (t t' : List I) (d : ℕ)

/-- The bounded window's inclusion into the connected cyclotomic quotient. -/
def reservoirWindowMap : ExtendedAtMost D Sc t t' d →ₗ[k]
    ReservoirQuotient D Sc cutoff t t' :=
  (ELVRelationSpan D Sc cutoff t t').mkQ.comp (ExtendedAtMost D Sc t t' d).subtype

/-- Coordinates with values in the bounded window, extended linearly to the
whole finite quotient. Only the values on the window are canonical. -/
def reservoirWindowCoordinates : ReservoirQuotient D Sc cutoff t t' →ₗ[k]
    ExtendedAtMost D Sc t t' d :=
  (reservoirWindowMap D Sc cutoff t t' d).leftInverse

/-- Joint recovery includes affine crossings and ordered exterior products. -/
theorem reservoirWindowCoordinates_apply {N : ℕ} (hN : ∀ i, N ≤ cutoff i)
    (hb : d + 2 * t.length.choose 2 < N)
    (f : ExtendedAtMost D Sc t t' d) :
    reservoirWindowCoordinates D Sc cutoff t t' d
      ((ELVRelationSpan D Sc cutoff t t').mkQ f) = f := by
  apply LinearMap.leftInverse_apply_of_inj
  apply LinearMap.ker_eq_bot.mpr
  exact elv_quotient_injective_on_extendedAtMost D Sc hN hb

/-- Every linear coordinate change can be extracted on a bounded window.
It need not preserve the cyclotomic ideal, and no global quotient substitution
is asserted. In particular this allows bounded normalization once its linear
source-coordinate formula and its categorical realization have been proved. -/
theorem exists_bounded_reservoir_extraction {V : Type u} [AddCommGroup V] [Module k V]
    (φ : (coefficientObj D Sc t ⟶ coefficientObj D Sc t') →ₗ[k] V)
    {N : ℕ} (hN : ∀ i, N ≤ cutoff i) (hb : d + 2 * t.length.choose 2 < N) :
    ∃ recover : ReservoirQuotient D Sc cutoff t t' →ₗ[k] V,
      ∀ f ∈ ExtendedAtMost D Sc t t' d,
        recover ((ELVRelationSpan D Sc cutoff t t').mkQ f) = φ f := by
  refine ⟨φ.comp ((ExtendedAtMost D Sc t t' d).subtype.comp
    (reservoirWindowCoordinates D Sc cutoff t t' d)), ?_⟩
  intro f hf
  change φ ((reservoirWindowCoordinates D Sc cutoff t t' d
    ((ELVRelationSpan D Sc cutoff t t').mkQ f)).val) = φ f
  rw [reservoirWindowCoordinates_apply D Sc cutoff t t' d hN hb ⟨f, hf⟩]

end OddMath.QuiverHecke
