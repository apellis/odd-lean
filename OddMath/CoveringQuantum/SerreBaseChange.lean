import OddMath.CoveringQuantum.SerreIdeal
import Mathlib.RingTheory.Flat.Basic

/-!
# Change of coefficients in the Serre presentation

Serre relations commute with coefficient maps. Extension of scalars from a
field reflects membership in the defining ideal, using the injective inclusion
of the original quotient into its tensor product with the extension field.
-/

noncomputable section
open TensorProduct

namespace OddMath.CoveringQuantum

variable {k K I : Type*} [CommRing k] [CommRing K]

/-- Covering quantum binomials commute with coefficient homomorphisms. -/
theorem map_qpBinom (φ : k →+* K) (q : kˣ) (π : k) (n r : ℕ) :
    φ (qpBinom q π n r) = qpBinom (Units.map φ.toMonoidHom q) (φ π) n r := by
  induction n generalizing r with
  | zero => cases r <;> simp [qpBinom]
  | succ n ih =>
    cases r with
    | zero => simp [qpBinom]
    | succ r => simp [qpBinom, ih, map_mul, map_add, map_pow, Units.coe_map, Units.coe_map_inv]

namespace SuperCartanDatum

variable (C : SuperCartanDatum I) (φ : k →+* K) (q : kˣ) (π : k)

/-- The bicharacter commutes with coefficient transport. -/
theorem map_chi (i j : I) :
    φ (C.chi q π i j) = C.chi (Units.map φ.toMonoidHom q) (φ π) i j := by
  simp only [chi_apply, map_mul, map_pow, ← map_zpow, Units.coe_map]
  rfl

/-- The normalization commutes with coefficient transport when its denominator is a unit. -/
theorem map_norm (i : I)
    (hu : IsUnit (1 - C.pii π i * ((C.qi q i : kˣ) : k) ^ 2)) :
    φ (C.norm q π i) = C.norm (Units.map φ.toMonoidHom q) (φ π) i := by
  have hp : φ (1 - C.pii π i * ((C.qi q i : kˣ) : k) ^ 2) =
      1 - C.pii (φ π) i * ((C.qi (Units.map φ.toMonoidHom q) i : Kˣ) : K) ^ 2 := by
    simp [pii, qi]
  obtain ⟨u, hu⟩ := hu
  unfold norm
  rw [← hp, ← hu]
  change φ (Ring.inverse (u : k)) = Ring.inverse ((Units.map φ.toMonoidHom u : Kˣ) : K)
  simp only [Ring.inverse_unit, Units.coe_map_inv]
  rfl

/-- Change of coefficients preserves a Serre coefficient. -/
theorem map_serreCoeff (i j : I) (r : ℕ) :
    φ (C.serreCoeff q π i j r) =
      C.serreCoeff (Units.map φ.toMonoidHom q) (φ π) i j r := by
  simp [serreCoeff, pii, qi, map_qpBinom, map_mul, map_pow]

/-- Change of coefficients preserves the entire Serre element. -/
theorem mapCoeffs_serreElt (i j : I) :
    FreeAlgebra.mapCoeffs φ (C.serreElt q π i j) =
      C.serreElt (Units.map φ.toMonoidHom q) (φ π) i j := by
  simp only [serreElt, map_sum, FreeAlgebra.mapCoeffs_smul, C.map_serreCoeff,
    map_mul, map_pow, PreF.θ, FreeAlgebra.mapCoeffs_ι]

/-- Coefficient homomorphisms carry the Serre ideal into the corresponding ideal. -/
theorem mapCoeffs_mem_serreIdeal {x : PreF k I} (hx : x ∈ C.serreIdeal q π) :
    FreeAlgebra.mapCoeffs φ x ∈ C.serreIdeal (Units.map φ.toMonoidHom q) (φ π) := by
  let g := (C.toSerreF (Units.map φ.toMonoidHom q) (φ π)).toRingHom.comp
    (FreeAlgebra.mapCoeffs φ)
  have hle : C.serreIdeal q π ≤ TwoSidedIdeal.ker g := by
    apply C.serreIdeal_le q π
    intro i j hij
    rw [TwoSidedIdeal.mem_ker]
    change C.toSerreF _ _ (FreeAlgebra.mapCoeffs φ (C.serreElt q π i j)) = 0
    rw [C.mapCoeffs_serreElt, C.toSerreF_serreElt _ _ hij]
  exact (C.mem_serreIdeal _ _ _).mpr ((TwoSidedIdeal.mem_ker g).mp (hle hx))

end SuperCartanDatum

namespace SuperCartanDatum

variable {k K I : Type*} [Field k] [Field K] [Algebra k K]
  (C : SuperCartanDatum I) (q : kˣ) (π : k)

/-- Extension of fields reflects the Serre ideal, via a faithful tensor inclusion. -/
theorem mapCoeffs_mem_serreIdeal_iff (x : PreF k I) :
    FreeAlgebra.mapCoeffs (algebraMap k K) x ∈
      C.serreIdeal (Units.map (algebraMap k K).toMonoidHom q) (algebraMap k K π) ↔
      x ∈ C.serreIdeal q π := by
  refine ⟨?_, C.mapCoeffs_mem_serreIdeal (algebraMap k K) q π⟩
  intro hx
  let A := C.serreF q π
  let inc : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let g : PreF K I →ₐ[K] K ⊗[k] A :=
    FreeAlgebra.lift K fun i ↦ inc (C.toSerreF q π (PreF.θ k i))
  have hg (y : PreF k I) :
      g (FreeAlgebra.mapCoeffs (algebraMap k K) y) = inc (C.toSerreF q π y) := by
    induction y using FreeAlgebra.induction with
    | grade0 c =>
      rw [FreeAlgebra.mapCoeffs_algebraMap, g.commutes, (C.toSerreF q π).commutes]
      change algebraMap K (K ⊗[k] A) (algebraMap k K c) = inc (algebraMap k A c)
      rw [inc.commutes]
      rfl
    | grade1 i => simp [g, PreF.θ]
    | mul a b ha hb => simp only [map_mul, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hr : ∀ a b,
      C.SerreRel (Units.map (algebraMap k K).toMonoidHom q) (algebraMap k K π) a b →
        g a = g b := by
    intro a b h
    cases h with
    | serre i j hij =>
      rw [← C.mapCoeffs_serreElt (algebraMap k K) q π, hg,
        C.toSerreF_serreElt q π hij, map_zero, map_zero]
  let G := RingQuot.liftAlgHom K ⟨g, hr⟩
  apply (C.mem_serreIdeal q π x).mpr
  apply Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  change inc (C.toSerreF q π x) = inc 0
  rw [map_zero, ← hg]
  have he : G (C.toSerreF _ _ (FreeAlgebra.mapCoeffs (algebraMap k K) x)) =
      g (FreeAlgebra.mapCoeffs (algebraMap k K) x) :=
    RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
  rw [← he, (C.mem_serreIdeal _ _ _).mp hx, map_zero]

end SuperCartanDatum
end OddMath.CoveringQuantum
