import OddMath.CoveringQuantum.SerreBaseChange
import OddMath.CoveringQuantum.PreF.BaseChange
import OddMath.CoveringQuantum.Twistor.Nondegenerate
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Negative-sign nondegeneracy over the original field

Extend to an algebraic closure, apply the twisting theorem there, and reflect
Serre-ideal membership using the tensor inclusion. The resulting theorem no
longer assumes that the coefficient field contains a square root of minus one.
This is a field theorem, not yet the generic covering-ring theorem.
-/

noncomputable section
namespace OddMath.CoveringQuantum.SuperCartanDatum

variable {k I : Type*} [Field k] [CharZero k] [DecidableEq I] [Finite I]
  (C : SuperCartanDatum I) (q : kˣ) (hC : C.BarConsistent)
  (hq : Transcendental ℚ (q : k))

include hC hq in
/-- The negative-sign Serre ideal is the form radical over any characteristic-zero
field with transcendental parameter and finite bar-consistent Cartan data. -/
theorem serreIdeal_neg_one_eq_radical_of_transcendental :
    C.serreIdeal q (-1) = PreF.radical (C.chi q (-1)) (C.norm q (-1)) := by
  let K := AlgebraicClosure k
  let φ := algebraMap k K
  let qK := Units.map φ.toMonoidHom q
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) (show 0 < 2 by decide)
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let t : Kˣ := Units.mk0 a ha0
  have ht : t ^ 2 = -1 := by apply Units.ext; exact ha
  have hqK : Transcendental ℚ (qK : K) :=
    (transcendental_algebraMap_iff φ.injective).mpr hq
  have hχ (i j : I) : φ (C.chi q (-1) i j) = C.chi qK (-1) i j := by
    simpa only [map_neg, map_one] using C.map_chi φ q (-1) i j
  have hn (i : I) : φ (C.norm q (-1) i) = C.norm qK (-1) i := by
    simp only [norm, Ring.inverse_eq_inv' (G₀ := k), Ring.inverse_eq_inv' (G₀ := K)]
    simp [pii, qi, qK]
  apply le_antisymm (C.serreIdeal_le_radical q (-1) (by simp))
  intro x hx
  apply (C.mapCoeffs_mem_serreIdeal_iff (K := K) q (-1) x).mp
  change FreeAlgebra.mapCoeffs φ x ∈ C.serreIdeal qK (φ (-1))
  rw [map_neg, map_one, C.serreIdeal_neg_one_eq_radical qK t hC ht hqK]
  exact PreF.mapCoeffs_mem_radical φ _ _ _ _ hχ hn hx

include hC hq in
/-- Nondegeneracy at the negative sign over the original characteristic-zero field. -/
theorem serreForm_neg_one_nondegenerate_of_transcendental :
    (C.serreForm q (-1) (by simp)).Nondegenerate :=
  (C.serreForm_nondegenerate_iff_ideal_eq q (-1) (by simp)).mpr
    (C.serreIdeal_neg_one_eq_radical_of_transcendental q hC hq)

end OddMath.CoveringQuantum.SuperCartanDatum
