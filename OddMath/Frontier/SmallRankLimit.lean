import OddMath.Frontier.SmallRank
import OddMath.Frontier.OddSymmetricLimit
import OddMath.Frontier.OddGrassmannSchur
import OddMath.Frontier.EKLSectionTwoG

/-!
# Ranks `0` and `1`: `OΛ → OΛ_a`, (5.3) and Conjecture 5.3

EKL arXiv:1111.1320v1, §5, pp. 44–46, for every rank `a ≥ 0`.

* `piAll N : OΛ → OΛ_N` for every `N` (`OddSymmetricLimit.piA` for `N ≥ 2`), surjective
  (`piAll_surjective`, from Prop 2.2 in every rank).
* **(5.3)** for every `N`: `OΛ/⟨ε_m : m > N⟩ ≅ OΛ_N` (`equation_5_3_all`), and the transition maps
  `OΛ_{N+1} → OΛ_N` for every `N` (`transitionAll`, compatible with the maps from `OΛ`). The
  inverse limit (`OddSymmetricLimit.inverse_limit`) is over the cofinal ranks `a ≥ 2`; the ranks
  `0, 1` do not change it.
* **Conjecture 5.3** for `a ≤ 1` (`conjecture_5_3_small`): `π_a(s_λ) = x^{λ_1}` if `λ` has at most
  `a` rows (the odd Schur polynomial `schurAll a λ`), and `0` otherwise. For `a ≥ 2` this is
  `OddGrassmannSchur.conjecture_5_3`.
-/

namespace OddMath.Frontier.SmallRank
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open EKRadicalQuotient (Q)
open OddLREKIdentification (piN sK)
open OddSymmetricLimit (elemIdeal)
open scoped BigOperators

set_option synthInstance.maxHeartbeats 200000

noncomputable section

/-! ## `OΛ → OΛ_N` and (5.3) in every rank -/

theorem piN_mem_OLam (N : ℕ) (x : Q) : piN N x ∈ OLam N := by
  match N with
  | 0 => exact mem_OLam_small (by omega) _
  | 1 => exact mem_OLam_small le_rfl _
  | n+2 => exact OddLREKIdentification.piN_mem_kernel n x

/-- `OΛ → OΛ_N`, `h_k ↦ h_k`, `ε_k ↦ ε_k`, every `N`. -/
def piAll (N : ℕ) : Q →+* OLam N := (piN N).codRestrict _ (piN_mem_OLam N)

@[simp] theorem piAll_coe (N : ℕ) (x : Q) : (piAll N x : SkewPolynomial N) = piN N x := rfl

theorem piAll_surjective (N : ℕ) : Function.Surjective (piAll N) := by
  rintro ⟨f, hf⟩
  rw [OLam_eq_elementaryClosure] at hf
  have hle : Subring.closure
      {f | ∃ k, 1 ≤ k ∧ k ≤ N ∧ f = FiniteCompleteElementary.elementaryPoly N k} ≤
      (piN N).range := by
    apply Subring.closure_le.mpr
    rintro _ ⟨k, _, _, rfl⟩
    exact ⟨EKElementaryQuotient.e k, OddLREKIdentification.piN_e _ _⟩
  obtain ⟨x, hx⟩ := hle hf
  exact ⟨x, Subtype.ext hx⟩

theorem piAll_eq_zero_iff (N : ℕ) (x : Q) : piAll N x = 0 ↔ x ∈ elemIdeal N := by
  rw [← OddSymmetricLimit.piN_eq_zero_iff_mem_elemIdeal, ← piAll_coe]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

/-- **EKL (5.3)** (p. 44), every rank `N`: `OΛ_N ≅ OΛ/⟨ε_m : m > N⟩`, induced by `π_N`. For
`N = n+2` this is `OddSymmetricLimit.equation_5_3`; in particular `OΛ/⟨ε_m : m > 0⟩ ≅ ℤ` and
`OΛ/⟨ε_m : m > 1⟩ ≅ ℤ[x]`. -/
def equation_5_3_all (N : ℕ) : Q ⧸ (elemIdeal N).asIdeal ≃+* OLam N :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift _ (piAll N) (fun x hx =>
      (piAll_eq_zero_iff N x).mpr (TwoSidedIdeal.mem_asIdeal.mp hx)))
    ⟨by
      intro y₁ y₂ hy
      obtain ⟨x₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
      obtain ⟨x₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
      rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk] at hy
      have hv := congrArg Subtype.val hy
      simp only [piAll_coe] at hv
      rw [Ideal.Quotient.eq]
      refine TwoSidedIdeal.mem_asIdeal.mpr ((piAll_eq_zero_iff N _).mp (Subtype.ext ?_))
      rw [piAll_coe, map_sub, hv, sub_self]
      exact (ZeroMemClass.coe_zero _).symm,
     by
      intro y
      obtain ⟨x, rfl⟩ := piAll_surjective N y
      exact ⟨Ideal.Quotient.mk _ x, Ideal.Quotient.lift_mk _ _ _⟩⟩

@[simp] theorem equation_5_3_all_mk (N : ℕ) (x : Q) :
    equation_5_3_all N (Ideal.Quotient.mk _ x) = piAll N x := rfl

theorem equation_5_3_all_symm_piAll (N : ℕ) (x : Q) :
    (equation_5_3_all N).symm (piAll N x) = Ideal.Quotient.mk _ x := by
  apply (equation_5_3_all N).injective
  rw [RingEquiv.apply_symm_apply, equation_5_3_all_mk]

/-- The transition map `OΛ_{N+1} → OΛ_N` (EKL p. 44), every `N`; for `N = n+2` see
`OddSymmetricLimit.transition`. -/
def transitionAll (N : ℕ) : OLam (N+1) →+* OLam N :=
  (Ideal.Quotient.lift (elemIdeal (N+1)).asIdeal (piAll N) (fun x hx =>
    (piAll_eq_zero_iff N x).mpr (OddSymmetricLimit.elemIdeal_mono (M := N) (N := N+1)
      (by omega) (TwoSidedIdeal.mem_asIdeal.mp hx)))).comp
    (equation_5_3_all (N+1)).symm.toRingHom

@[simp] theorem transitionAll_piAll (N : ℕ) (x : Q) :
    transitionAll N (piAll (N+1) x) = piAll N x := by
  simp only [transitionAll, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, equation_5_3_all_symm_piAll, Ideal.Quotient.lift_mk]

theorem elementary_mem_OLam (N j : ℕ) : FiniteCompleteElementary.elementaryPoly N j ∈ OLam N := by
  have h := (piAll N (EKElementaryQuotient.e j)).2
  rwa [piAll_coe, OddLREKIdentification.piN_e] at h

/-- `ε_j ∈ OΛ_N`. -/
def eAll (N j : ℕ) : OLam N := ⟨_, elementary_mem_OLam N j⟩

/-- The transition maps send `ε_j` to `ε_j` (which is `0` for `j > N`). -/
theorem transitionAll_eAll (N j : ℕ) : transitionAll N (eAll (N+1) j) = eAll N j := by
  have h (M : ℕ) : eAll M j = piAll M (EKElementaryQuotient.e j) :=
    Subtype.ext (by rw [piAll_coe, OddLREKIdentification.piN_e]; rfl)
  rw [h, h, transitionAll_piAll]

/-! ## Conjecture 5.3 in ranks `0` and `1` -/

theorem shapePrefix_le_card (μ : YoungDiagram) (k : ℕ) :
    TableauDominance.shapePrefix μ k ≤ μ.card :=
  Finset.card_filter_le _ _

theorem shapePrefix_one_row {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    TableauDominance.shapePrefix μ k = μ.card := by
  rw [TableauDominance.shapePrefix, Finset.filter_true_of_mem]
  intro p hp
  have h0 : (p.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) hp
  have := YoungDiagram.mem_iff_lt_colLen.mp h0
  omega

/-- A diagram with at most one row is maximal for dominance, so `s_λ = h_λ` in `OΛ`. -/
theorem sK_one_row {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ 1) :
    sK μ = EKPartitionSpanning.hPartition μ := by
  have hbot : EKLSectionTwo.UpSQ μ = ⊥ := by
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨κ, hcard, hdom, hne, rfl⟩
    refine absurd (EKLemma311Cond.dom_antisymm hdom fun k => ?_) (Ne.symm hne)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [EKLemma311Cond.shapePrefix_zero, EKLemma311Cond.shapePrefix_zero]
    · rw [shapePrefix_one_row hμ hk, ← hcard]
      exact shapePrefix_le_card κ k
  have h := EKLSectionTwo.sK_sub_mem_upSQ μ
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at h
  exact h

theorem generator_pow_eq_monomial (k : ℕ) :
    (generator 0 : SkewPolynomial 1) ^ k = monomial (fun _ => k) 1 :=
  rankOneEquiv.injective (by rw [map_pow, rankOneEquiv_generator, rankOneEquiv_monomial,
    Polynomial.X_pow_eq_monomial])

/-- **EKL Conjecture 5.3** (p. 46) in ranks `a ≤ 1`: `π_a(s_λ)` is the odd Schur polynomial
`s_λ = x^λ` (EKL (2.69) in rank `a`, `schurAll`) when `λ` has at most `a` rows, and `0`
otherwise. For `a = n+2` this is `OddGrassmannSchur.conjecture_5_3`. -/
theorem conjecture_5_3_small {N : ℕ} (hN : N ≤ 1) (lam : YoungDiagram) :
    piN N (sK lam) = if lam.colLen 0 ≤ N then schurAll N (fun i => lam.rowLen i) else 0 := by
  split_ifs with h
  · rw [sK_one_row (h.trans hN), schurAll_small hN, EKPartitionSpanning.hPartition,
      map_list_prod, List.map_map, YoungDiagram.rowLens]
    rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
    · rw [show lam.colLen 0 = 0 by omega, List.range_zero, List.map_nil, List.map_nil,
        List.prod_nil, exp_zero_eq (fun i => _)]
      rfl
    · rcases (by omega : lam.colLen 0 = 0 ∨ lam.colLen 0 = 1) with h0 | h1
      · have hr : lam.rowLen 0 = 0 :=
          EKLemma311Cond.rowLen_eq_zero_of_colLen_le lam (by omega)
        rw [h0, List.range_zero, List.map_nil, List.map_nil, List.prod_nil]
        have : (fun i : Fin 1 => lam.rowLen i) = 0 := funext fun i => by
          rw [Fin.fin_one_eq_zero i]; exact hr
        rw [this]
        rfl
      · rw [h1, show List.range 1 = [0] from rfl, List.map_singleton, List.map_singleton,
          List.prod_singleton, Function.comp_apply, OddLREKIdentification.piN_h, completePoly_one,
          generator_pow_eq_monomial]
        congr 1
        funext i
        rw [Fin.fin_one_eq_zero i]
        rfl
  · exact (OddLRThm38.thm38_tall N lam (Nat.lt_of_not_le h)).1

end

end OddMath.Frontier.SmallRank
