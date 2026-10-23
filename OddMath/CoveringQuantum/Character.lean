import OddMath.CoveringQuantum.CharacterBaseChange
import OddMath.CoveringQuantum.Negative
import LieLean.Algebra.QuantumGroup.PBW.KostantDimension

/-!
# The character comparison

This proves Hill–Wang, arXiv:1202.2769v2, Lemma 6.11, for every super Cartan datum with finitely
many simple roots (`SuperCartanDatum.finrank_serreWeightSpace_one_eq_neg_one`): both
specializations have the weight dimensions `K(ν)` of the Kac–Moody algebra of the Cartan matrix.
For bar-consistent data the ordered twistor also compares the negative specialization at `q` with
the ordinary specialization at `t * q`, where `t² = -1`
(`SuperCartanDatum.finrank_serreWeightSpace_twist`).
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

open FreeAlgebra Matrix.Realization.SuperEnveloping

variable {I k : Type*} [DecidableEq I] [Finite I] [Field k] [CharZero k]
  (C : SuperCartanDatum I) {q : kˣ}

/-- At `π = -1`, the kernel of `'f → f` on the words of weight `ν` is the span of the products
`a sᵢⱼ b` of weight `ν`, so the weight space of `f` and this span have complementary
dimensions. -/
theorem finrank_serreWeightSpace_neg_one (hq : Transcendental ℚ (q : k)) (ν : I →₀ ℕ) :
    finrank k (C.serreWeightSpace q (-1) ν) +
      finrank k (productSpan (C.serreFamily q) (superSerreWeight C.a) ν) =
        Fintype.card (LusztigF.Words ν) := by
  set V := LusztigF.weightSpace k ν
  set Z := productSpan (C.serreFamily q) (superSerreWeight C.a) ν
  set f := (C.toSerreF q (-1)).toLinearMap.domRestrict V
  have hZV : Z ≤ V := productSpan_le_wordSpan (fun ij ↦ C.serreElt_mem_wordSpan q (-1) ij) ν
  have hrange : LinearMap.range f = C.serreWeightSpace q (-1) ν := by
    rw [LinearMap.range_domRestrict]
    rfl
  have hker : LinearMap.ker f = Z.comap V.subtype := by
    ext y
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · refine (C.mem_productSpan_of_mem_radical hq ν).1 y ?_ y.2
      exact C.serreIdeal_le_radical q (-1) (by norm_num) ((C.mem_serreIdeal q (-1) y).2 h)
    · exact (C.mem_serreIdeal q (-1) y).1 (C.serreFamily_mem_serreIdeal q h)
  have hZ : finrank k (Z.comap V.subtype) = finrank k Z := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_eq_right.2 hZV]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker, hZ, LusztigF.finrank_weightSpace] at hrn
  exact hrn

/-- **Hill–Wang, arXiv:1202.2769v2, Lemma 6.11**, for every super Cartan datum with finitely
many simple roots: the two specializations `π = 1` and `π = -1` have equal dimensions in every
weight. Both equal `K(ν)`, Kostant's partition function of the Kac–Moody algebra of the Cartan
matrix: at `π = 1` by quantum Gabber–Kac, at `π = -1` by the super Serre count
(`SuperCartanDatum.finrank_productSpan_neg_one`). The argument is ours. -/
theorem finrank_serreWeightSpace_one_eq_neg_one (hq : Transcendental ℚ (q : k)) (ν : I →₀ ℕ) :
    finrank k (C.serreWeightSpace q 1 ν) = finrank k (C.serreWeightSpace q (-1) ν) := by
  have := Fintype.ofFinite I
  have h₁ := C.finrank_serreWeightSpace_one q hq ν
  have h₂ := C.finrank_serreWeightSpace_neg_one hq ν
  have hA : C.lusztigDatum.cartanMatrix = C.a := by
    ext i j; exact lusztigDatum_cartanMatrix C i j
  let P := Matrix.Realization.std C.lusztigDatum.cartanMatrix ℚ
  have h₃ := LusztigF.kostantPartition_add_finrank_serreSpan C.lusztigDatum P ν
  have key : ∀ (A : Matrix I I ℤ) (_ : A = C.a) {H : Type _} [AddCommGroup H] [Module ℚ H]
      [FiniteDimensional ℚ H] (P : Matrix.Realization A ℚ H),
      Matrix.Realization.KacMoodyAlgebra.kostantPartition P (P.rootOf (natVec ν)) +
        finrank k (productSpan (C.serreFamily q) (superSerreWeight C.a) ν) =
          Fintype.card (LusztigF.Words ν) := by
    rintro A rfl H _ _ _ P
    exact C.finrank_productSpan_neg_one hq P ν
  have h₄ := key _ hA P
  change Matrix.Realization.KacMoodyAlgebra.kostantPartition P (P.rootOf fun i ↦ (ν i : ℤ)) + _ = _ at h₄
  omega

end SuperCartanDatum
end OddMath.CoveringQuantum
