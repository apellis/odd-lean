import OddMath.CoveringQuantum.SerreBaseChange
import OddMath.CoveringQuantum.Coefficients.Splitting

/-!
# Detection of the generic Serre ideal by its sign fibers

Central idempotents lift the two specialized ideals back into the generic
presentation. This proves ideal membership detection, not merely detection
of equality among scalar coefficients.
-/

noncomputable section
namespace OddMath.CoveringQuantum
namespace SuperCartanDatum

variable {k K I : Type*} [CommRing k] [CommRing K]
  (C : SuperCartanDatum I) (q : kˣ) (π : k)

/-- An idempotent coefficient retraction lifts membership in a specialized Serre ideal. -/
theorem smul_mem_serreIdeal_of_mapCoeffs (φ : k →+* K) (σ : K →+* k)
    (e : k) (he : e * e = e) (hr : ∀ a, e * σ (φ a) = e * a)
    {x : PreF k I}
    (hx : FreeAlgebra.mapCoeffs φ x ∈ C.serreIdeal (Units.map φ.toMonoidHom q) (φ π)) :
    e • x ∈ C.serreIdeal q π := by
  have hm (y : PreF k I) :
      e • FreeAlgebra.mapCoeffs σ (FreeAlgebra.mapCoeffs φ y) = e • y := by
    induction y using FreeAlgebra.induction_wordBasis with
    | zero => simp
    | add y z hy hz => simp only [map_add, smul_add, hy, hz]
    | smul c y hy =>
      rw [FreeAlgebra.mapCoeffs_smul, FreeAlgebra.mapCoeffs_smul, smul_smul, hr,
        mul_comm e c, mul_smul, hy, smul_comm]
    | word w => rw [FreeAlgebra.mapCoeffs_wordBasis, FreeAlgebra.mapCoeffs_wordBasis]
  let g : PreF K I →ₙ+* C.serreF q π :=
    { toFun := fun y ↦ e • C.toSerreF q π (FreeAlgebra.mapCoeffs σ y)
      map_zero' := by simp
      map_add' := by intro y z; simp [smul_add]
      map_mul' := by intro y z; simp only [map_mul, smul_mul_smul_comm, he] }
  have hle : C.serreIdeal (Units.map φ.toMonoidHom q) (φ π) ≤ TwoSidedIdeal.ker g := by
    apply C.serreIdeal_le
    intro i j hij
    rw [TwoSidedIdeal.mem_ker]
    change e • C.toSerreF q π (FreeAlgebra.mapCoeffs σ
      (C.serreElt (Units.map φ.toMonoidHom q) (φ π) i j)) = 0
    rw [← C.mapCoeffs_serreElt φ q π, ← map_smul, hm, map_smul,
      C.toSerreF_serreElt q π hij, smul_zero]
  have h := (TwoSidedIdeal.mem_ker g).mp (hle hx)
  change e • C.toSerreF q π (FreeAlgebra.mapCoeffs σ (FreeAlgebra.mapCoeffs φ x)) = 0 at h
  rw [← map_smul, hm] at h
  exact (C.mem_serreIdeal q π _).mpr h

end SuperCartanDatum

namespace Coefficients

/-- The central idempotent selecting the positive-sign fiber. -/
def positiveIdempotent : Ring := splitEquiv.symm (1, 0)

/-- The central idempotent selecting the negative-sign fiber. -/
def negativeIdempotent : Ring := splitEquiv.symm (0, 1)

@[simp] theorem split_positiveIdempotent : split positiveIdempotent = (1, 0) :=
  splitEquiv.apply_symm_apply _

@[simp] theorem split_negativeIdempotent : split negativeIdempotent = (0, 1) :=
  splitEquiv.apply_symm_apply _

@[simp] theorem split_algebraMap (c : RatFunc ℚ) :
    split (algebraMap (RatFunc ℚ) Ring c) = (c, c) := split.commutes c

theorem positiveIdempotent_mul_self : positiveIdempotent * positiveIdempotent = positiveIdempotent := by
  apply split_injective
  simp only [map_mul, split_positiveIdempotent]
  ext <;> simp

theorem negativeIdempotent_mul_self : negativeIdempotent * negativeIdempotent = negativeIdempotent := by
  apply split_injective
  simp only [map_mul, split_negativeIdempotent]
  ext <;> simp

theorem positiveIdempotent_add_negativeIdempotent : positiveIdempotent + negativeIdempotent = 1 := by
  apply split_injective
  simp only [map_add, map_one, split_positiveIdempotent, split_negativeIdempotent]
  ext <;> simp

theorem positiveIdempotent_retract (a : Ring) :
    positiveIdempotent * algebraMap (RatFunc ℚ) Ring (specialize 1 (one_pow 2) a) =
      positiveIdempotent * a := by
  apply split_injective
  simp only [map_mul, split_positiveIdempotent, split_algebraMap]
  ext <;> simp [split]

theorem negativeIdempotent_retract (a : Ring) :
    negativeIdempotent * algebraMap (RatFunc ℚ) Ring (specialize (-1) (by norm_num) a) =
      negativeIdempotent * a := by
  apply split_injective
  simp only [map_mul, split_negativeIdempotent, split_algebraMap]
  ext <;> simp [split]

variable {I : Type*} (C : SuperCartanDatum I)

/-- Membership in the generic Serre ideal is detected by the two sign specializations. -/
theorem mem_serreIdeal_iff_specialize (x : PreF Ring I) :
    x ∈ C.serreIdeal q pi ↔
      FreeAlgebra.mapCoeffs (specialize 1 (one_pow 2)).toRingHom x ∈
        C.serreIdeal (Units.map (specialize 1 (one_pow 2)).toMonoidHom q) 1 ∧
      FreeAlgebra.mapCoeffs (specialize (-1) (by norm_num)).toRingHom x ∈
        C.serreIdeal (Units.map (specialize (-1) (by norm_num)).toMonoidHom q) (-1) := by
  constructor
  · intro hx
    constructor
    · simpa using
        C.mapCoeffs_mem_serreIdeal (specialize 1 (one_pow 2)).toRingHom q pi hx
    · simpa using
        C.mapCoeffs_mem_serreIdeal (specialize (-1) (by norm_num)).toRingHom q pi hx
  · rintro ⟨hp, hm⟩
    have hp' := C.smul_mem_serreIdeal_of_mapCoeffs q pi
      (specialize 1 (one_pow 2)).toRingHom (algebraMap (RatFunc ℚ) Ring)
      positiveIdempotent positiveIdempotent_mul_self positiveIdempotent_retract
      (by simpa using hp)
    have hm' := C.smul_mem_serreIdeal_of_mapCoeffs q pi
      (specialize (-1) (by norm_num)).toRingHom (algebraMap (RatFunc ℚ) Ring)
      negativeIdempotent negativeIdempotent_mul_self negativeIdempotent_retract
      (by simpa using hm)
    simpa only [← add_smul, positiveIdempotent_add_negativeIdempotent, one_smul] using
      (C.serreIdeal q pi).add_mem hp' hm'

end Coefficients
end OddMath.CoveringQuantum
