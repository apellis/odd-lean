import OddMath.Frontier.SmallRank
import OddMath.Frontier.EKLSectionTwoH
import OddMath.Frontier.EKLSectionTwoB
import OddMath.Frontier.EKLSectionTwoC

/-!
# Ranks `0` and `1`: graded ranks, reduction mod 2, Corollary 2.6

EKL arXiv:1111.1320v1, §2.1–§2.2, for the ranks `a ≤ 1` omitted by the `a ≥ 2` statements.
Here `OΛ_a = OPol_a = ONH_a` (`OLam_small`), so every graded rank below is the graded rank of
`OPol_a`, `qrk(OPol_a) = Σ_d rk(OPol_a)_{2d} q^{2d}` (`EKLSectionTwo.qrkPol`, from the literal
monomial degree pieces).

* Prop 2.2, (2.18) and (2.20)/(2.28) for `a ≤ 1` (`symRank_mul_qPoch_small`,
  `qrk_symmetric_small`); (2.19)/(2.52) for `a ≤ 1` (`qrkPol_eq_small`); (2.44) for `a ≤ 1`
  (`eq_2_44_small`).
* (2.13)/(2.27) for `a ≤ 1`: `OΛ_a/2 ≅ Λ_a ⊗ ℤ/2` (`symmetricModTwo_small`).
* Cor 2.6 at `a = 1`: `OΛ_1[x_1] = OΛ_0[x_1]` (`cor_2_6_rank_one`).
-/

namespace OddMath.Frontier.SmallRank
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open EKLSectionTwo PowerSeries
open scoped BigOperators

set_option synthInstance.maxHeartbeats 200000

noncomputable section

/-! ## Graded ranks -/

theorem qfactorial_small {N : ℕ} (hN : N ≤ 1) : qfactorial N = 1 := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
  · rfl
  · simp [qfactorial, qint, qpow_zero]

theorem choose_two_small {N : ℕ} (hN : N ≤ 1) : N.choose 2 = 0 :=
  Nat.choose_eq_zero_of_lt (by omega)

theorem ofPS_tsq_one_sub_X : ofPS (tsq (1 - X)) = 1 - qpow 2 := by
  rw [map_sub, map_sub, map_one, map_one, tsq_X, ofPS_X_pow]
  rfl

theorem polRank_mul (N : ℕ) : polRank N * (1 - X) ^ N = 1 := by
  rw [polRank_eq]
  exact BoxPartitionCount.mgf_mul N

/-- **EKL Prop 2.2**, (2.18) first line, `a ≤ 1` (in `t = q²`): `qrk(OΛ_a) ∏_{i ≤ a} (1 - t^i) = 1`,
with `OΛ_a = OPol_a`. For `a ≥ 2` see `EKLSectionTwo.symRank_mul_qPoch`. -/
theorem symRank_mul_qPoch_small {N : ℕ} (hN : N ≤ 1) :
    polRank N * BoxPartitionCount.qPoch N = 1 := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
  · simpa [BoxPartitionCount.qPoch] using polRank_mul 0
  · simpa [BoxPartitionCount.qPoch] using polRank_mul 1

/-- **EKL Prop 2.2**, (2.20)/(2.28), `a ≤ 1`: `qrk(OΛ_a) [a]! (1 - q²)^a = q^{-a(a-1)/2}`, with
`OΛ_a = OPol_a`. For `a ≥ 2` see `EKLSectionTwo.qrk_symmetric`. -/
theorem qrk_symmetric_small {N : ℕ} (hN : N ≤ 1) :
    ofPS (qrkPol N) * qfactorial N * (1 - qpow 2) ^ N = qpow (-((N.choose 2 : ℕ) : ℤ)) := by
  have h := congrArg (fun f => ofPS (tsq f)) (polRank_mul N)
  simp only [map_mul, map_pow, map_one, ofPS_tsq_one_sub_X] at h
  rw [qfactorial_small hN, mul_one, qrkPol, h, choose_two_small hN]
  rfl

/-- **EKL (2.19)** (corrected; see ERRATA.md) and (2.52), `a ≤ 1`: `qrk(OPol_a) = qrk(OΛ_a)
Σ_{σ ∈ S_a} q^{2ℓ(σ)}`; here `OΛ_a = OPol_a` and `S_a` is trivial. For `a ≥ 2` see
`EKLSectionTwo.qrkPol_eq`. -/
theorem qrkPol_eq_small {N : ℕ} (hN : N ≤ 1) :
    qrkPol N = qrkPol N *
      ∑ w : Equiv.Perm (Fin N), (X : ℤ⟦X⟧) ^ (2 * NilHeckeGrading.inversions w) := by
  rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
  · rw [NilHeckeSmallRank.physical_rank_zero, mul_one]
  · rw [NilHeckeSmallRank.physical_rank_one, mul_one]

/-- **EKL (2.44)**, `a ≤ 1`: `rk_q ONH_a = q^{-a(a-1)/2}[a]!/(1 - q²)^a`, with
`ONH_a = OPol_a`. For `a ≥ 2` see `EKLMisc.eq_2_44`. -/
theorem eq_2_44_small {N : ℕ} (hN : N ≤ 1) :
    ofPS (qrkPol N) * (1 - qpow 2) ^ N = qpow (-((N.choose 2 : ℕ) : ℤ)) * qfactorial N := by
  have h := qrk_symmetric_small hN
  rw [qfactorial_small hN, mul_one] at h ⊢
  rw [h, choose_two_small hN]

/-! ## (2.13), (2.27): reduction mod 2 -/

theorem mem_symmetricSubalgebra_small {N : ℕ} (hN : N ≤ 1) (p : Pol2 N) :
    p ∈ MvPolynomial.symmetricSubalgebra (Fin N) (ZMod 2) := by
  rw [MvPolynomial.mem_symmetricSubalgebra]
  intro e
  have he : e = 1 := Equiv.ext fun i =>
    Fin.ext (by have := (e i).isLt; have := i.isLt; simp; omega)
  rw [he, Equiv.Perm.coe_one, MvPolynomial.rename_id, AlgHom.id_apply]

/-- `OΛ_a → Λ_a ⊗ ℤ/2`, `a ≤ 1`. -/
def reduceSymmetricSmall {N : ℕ} (hN : N ≤ 1) :
    OLam N →+* MvPolynomial.symmetricSubalgebra (Fin N) (ZMod 2) :=
  RingHom.codRestrict ((reduce N).comp (OLam N).subtype) _ fun _ =>
    mem_symmetricSubalgebra_small hN _

theorem reduceSymmetricSmall_surjective {N : ℕ} (hN : N ≤ 1) :
    Function.Surjective (reduceSymmetricSmall hN) := by
  rintro ⟨p, hp⟩
  obtain ⟨f, rfl⟩ := reduce_surjective N p
  exact ⟨⟨f, mem_OLam_small hN f⟩, rfl⟩

/-- **EKL (2.13), (2.27)**, `a ≤ 1`: `OΛ_a/ker ≅ Λ_a ⊗ ℤ/2`. For `a ≥ 2` see
`EKLSectionTwo.symmetricModTwo`. -/
def symmetricModTwo_small {N : ℕ} (hN : N ≤ 1) :
    OLam N ⧸ RingHom.ker (reduceSymmetricSmall hN) ≃+*
      MvPolynomial.symmetricSubalgebra (Fin N) (ZMod 2) :=
  RingHom.quotientKerEquivOfSurjective (reduceSymmetricSmall_surjective hN)

/-! ## Corollary 2.6 at `a = 1` -/

/-- **EKL Cor 2.6** at `a = 1`: `OΛ_1[x_1] = OΛ_0[x_1]` inside `OPol_1` (both are all of `OPol_1`).
For `a = 2` see `EKLSectionTwo.cor_2_6_rank_two`, for `a ≥ 3`
`ElementaryBranching.kernel_adjoin_last_eq`. -/
theorem cor_2_6_rank_one :
    Subring.closure ((OLam 1 : Set (SkewPolynomial 1)) ∪ {generator (Fin.last 0)}) =
      Subring.closure (Set.range (ElementaryBranching.«prefix» 0) ∪ {generator (Fin.last 0)}) := by
  have hx : ∀ S : Set (SkewPolynomial 1), generator (Fin.last 0) ∈ S →
      Subring.closure S = ⊤ := fun S hS =>
    eq_top_iff.mpr fun f _ => Subring.closure_mono (Set.singleton_subset_iff.mpr hS)
      (mem_closure_generator f)
  rw [hx _ (Or.inr rfl), hx _ (Or.inr rfl)]

end

end OddMath.Frontier.SmallRank
