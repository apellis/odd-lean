import OddMath.CoveringQuantum.CharacterBaseChange
import OddMath.CoveringQuantum.Negative

/-!
# The bar-consistent character comparison

This proves the finite bar-consistent case of Hill–Wang, arXiv:1202.2769v2,
Lemma 6.11 (`lem:sameCh`). The ordered twistor compares the negative specialization
at `q` with the ordinary specialization at `t * q`, where `t² = -1`.
Quantum Gabber–Kac removes the parameter shift, and scalar extension removes the
square-root hypothesis. The result is an intermediate input to Hill–Wang
Proposition 6.12 and BE2 Theorem 11.3: bar-consistency is an extra hypothesis for
that downstream theorem, whose general case is not asserted here.
-/

noncomputable section

namespace OddMath.CoveringQuantum

open Module LieLean

namespace PreF

private theorem wordGauge_weightSpace (k : Type*) [CommRing k] {I : Type*}
    (f : I → I → kˣ) (ν : I →₀ ℕ) :
    (weightSpace k ν).map (wordGauge f).toLinearMap = weightSpace k ν := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    change wordGauge f (monomial k w) ∈ weightSpace k ν
    rw [wordGauge_monomial]
    exact Submodule.smul_mem _ _ (hw ▸ monomial_mem_weightSpace w)
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨(wordGauge f).symm (monomial k w), ?_, by simp⟩
    rw [wordGauge_symm_monomial, Units.smul_def]
    exact Submodule.smul_mem _ _ (hw ▸ monomial_mem_weightSpace w)

end PreF

namespace SuperCartanDatum

variable {I k : Type*} [Field k] [CharZero k]
  (C : SuperCartanDatum I) (q t : kˣ)

private theorem transcendental_twisted_parameter (ht : t ^ 2 = -1)
    (hq : Transcendental ℚ (q : k)) : Transcendental ℚ ((t * q : kˣ) : k) := by
  have hta : IsAlgebraic ℚ (t : k) := by
    apply IsAlgebraic.of_pow (n := 2) (by decide)
    have h := congrArg (fun u : kˣ ↦ (u : k)) ht
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
    rw [h]
    exact isAlgebraic_one.neg
  intro h
  apply hq
  simpa [Units.val_mul, ← mul_assoc] using hta.inv.mul h

variable [LinearOrder I] [Finite I]

/-- The twistor preserves weight dimensions, with the required shift `q ↦ t * q`.
This is a linear comparison, not an algebra isomorphism of the ordinary products. -/
theorem finrank_serreWeightSpace_twist (hC : C.BarConsistent) (ht : t ^ 2 = -1)
    (hq : Transcendental ℚ (q : k)) (ν : I →₀ ℕ) :
    finrank k (C.serreWeightSpace (t * q) 1 ν) =
      finrank k (C.serreWeightSpace q (-1) ν) := by
  let V := LusztigF.weightSpace k ν
  let f := (C.toSerreF (t * q) 1).toLinearMap.domRestrict V
  let g := ((C.toSerreF q (-1)).toLinearMap.comp (C.freeTwist t).toLinearMap).domRestrict V
  have hf : LinearMap.range f = C.serreWeightSpace (t * q) 1 ν := by
    rw [LinearMap.range_domRestrict]
    rfl
  have hg : LinearMap.range g = C.serreWeightSpace q (-1) ν := by
    rw [LinearMap.range_domRestrict, Submodule.map_comp]
    change ((PreF.weightSpace k ν).map (C.freeTwist t).toLinearMap).map _ = _
    rw [freeTwist, PreF.wordGauge_weightSpace]
    rfl
  have hk : LinearMap.ker f = LinearMap.ker g := by
    ext x
    change C.toSerreF (t * q) 1 x = 0 ↔ C.toSerreF q (-1) (C.freeTwist t x) = 0
    rw [← C.mem_serreIdeal, ← C.mem_serreIdeal,
      C.serreIdeal_one_eq_radical (t * q) (transcendental_twisted_parameter q t ht hq),
      C.serreIdeal_neg_one_eq_radical q t hC ht hq]
    exact (C.freeTwist_mem_radical_iff q t hC ht x).symm
  have h₁ := LinearMap.finrank_range_add_finrank_ker f
  have h₂ := LinearMap.finrank_range_add_finrank_ker g
  rw [hf] at h₁
  rw [hg, ← hk] at h₂
  omega

end SuperCartanDatum

namespace SuperCartanDatum

variable {I k : Type*} [DecidableEq I] [Finite I] [Field k] [CharZero k]
  (C : SuperCartanDatum I) (q : kˣ)

/-- Hill–Wang, arXiv:1202.2769v2, Lemma 6.11, for finite bar-consistent data:
the two specializations have equal dimensions in every weight. This intermediate
statement retains bar-consistency, an extra hypothesis relative to BE2 Theorem 11.3;
the general case without it remains separate. -/
theorem finrank_serreWeightSpace_one_eq_neg_one (hC : C.BarConsistent)
    (hq : Transcendental ℚ (q : k)) (ν : I →₀ ℕ) :
    finrank k (C.serreWeightSpace q 1 ν) = finrank k (C.serreWeightSpace q (-1) ν) := by
  let K := AlgebraicClosure k
  let φ := algebraMap k K
  let qK := Units.map φ.toMonoidHom q
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K) (show 0 < 2 by decide)
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let t : Kˣ := Units.mk0 a ha0
  have ht : t ^ 2 = -1 := by apply Units.ext; exact ha
  have hqK : Transcendental ℚ (qK : K) :=
    (transcendental_algebraMap_iff φ.injective).mpr hq
  let := Fintype.ofFinite I
  let o : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have htq := transcendental_twisted_parameter qK t ht hqK
  calc
    finrank k (C.serreWeightSpace q 1 ν) =
        finrank K (C.serreWeightSpace (t * qK) 1 ν) :=
      C.finrank_serreWeightSpace_one_eq q hq (t * qK) htq ν
    _ = finrank K (C.serreWeightSpace qK (-1) ν) :=
      C.finrank_serreWeightSpace_twist qK t hC ht hqK ν
    _ = finrank k (C.serreWeightSpace q (-1) ν) := by
      have h := C.finrank_serreWeightSpace_baseChange (K := K) q (-1) ν
      have hπ : algebraMap k K (-1) = -1 := by simp
      rw [hπ] at h
      exact h.symm

end SuperCartanDatum
end OddMath.CoveringQuantum
