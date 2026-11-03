import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerPolynomialCap

/-! # First odd polynomial-cap closure at nonpositive height

This evaluates the first normalized candidate moment in
`SwappedVacuumNonpositiveBubbles.md`, §§3–4, with the original extraction
row and signed dot on literal A/T. The chosen mixed-cap identification is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- For probe degree 2M at most the reservoir degree, the first normalized
polynomial-cap closure equals the actual first higher moment on all vectors. -/
theorem polynomialCapMoment_nonpositive_first (i : I) (hN : 0 < cutoff i) (M : ℕ)
    (hMN : 2 * M ≤ cutoff i) :
    polynomialCapMoment D Sc cutoff L i hN M (cutoff i - 2 * M) =
      momentMap D Sc cutoff L i hN (cutoff i) := by
  rw [polynomialCapMoment_sum]
  calc
    _ = M.choose M • momentMap D Sc cutoff L i hN (2 * M + (cutoff i - 2 * M)) := by
      apply Finset.sum_eq_single M
      · intro j hj hjM
        have hjle : j ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hjlt : j < M := by omega
        have hn : 2 * j + (cutoff i - 2 * M) < cutoff i := by omega
        have hne : 2 * j + (cutoff i - 2 * M) + 1 ≠ cutoff i := by omega
        have hz : momentMap D Sc cutoff L i hN (2 * j + (cutoff i - 2 * M)) = 0 := by
          apply LinearMap.ext
          intro z
          change momentMap D Sc cutoff L i hN _ z = 0
          have h := functional_dot_window D Sc cutoff L i hN _ hn z
          change momentMap D Sc cutoff L i hN _ z =
            if 2 * j + (cutoff i - 2 * M) + 1 = cutoff i then z else 0 at h
          simpa only [ite_eq_right hne] using h
        rw [hz, nsmul_zero]
      · simp
    _ = _ := by rw [Nat.choose_self, one_nsmul, Nat.add_sub_of_le hMN]

/-- The first odd closure has the original left exterior coefficient and the
reservoir-cutoff sign, for zero and negative external height alike. -/
theorem polynomialCapMoment_nonpositive_first_odd (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (M : ℕ) (hMN : 2 * M ≤ cutoff i) :
    polynomialCapMoment D Sc cutoff L i hN M (cutoff i - 2 * M) =
      LinearMap.mulLeft k ((-1 : k) ^ (cutoff i + 1) •
        coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) := by
  rw [polynomialCapMoment_nonpositive_first D Sc cutoff L i hN M hMN,
    momentMap_first_odd D Sc cutoff L i hi hN]

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
