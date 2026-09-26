import OddMath.Frontier.OddLRMisc
import OddMath.Frontier.OddLRTableau

/-! Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), Remark 4.10, (4.10),
p. 15, for the odd Littlewood–Richardson coefficient `c^λ_{μν} = OddLRTableau.oddLR λ μ ν`
(E Definition 4.6):

* `c^λ_{μν} = (-1)^{dN(μ)+dN(ν)+dN(λ)+N(μ)+N(ν)+N(λ)} c^λ_{νμ}` (`remark_4_10_reverse`), from
  the ordinary anti-involution `R` (E (2.9b), corrected as in `OddLRMisc.reverse_sK_source`);
* `c^λ_{μν} = (-1)^{NE(μ)+NE(ν)+NE(λ)} c^{λᵀ}_{μᵀνᵀ}` (`remark_4_10_transpose`), from
  `ψ₁ψ₂` (E (2.9a)) and `(-1)^{ℓ(w_λ)} = (-1)^{NE(λ)}` (`ell_eq_northEast`);
* `c^λ_{μμ} ≠ 0 ⇒ (-1)^{dN(λ)+N(λ)} = 1` (`remark_4_10_square`).

Also `c^λ_{μν} = 0` unless `|λ| = |μ| + |ν|` (E Definition 4.6, `oddLR_eq_zero_of_card`). -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace OddMath.Frontier.OddLRMisc

open EKRadicalQuotient (Q)
open EKAutomorphisms (reverseLinear psi12)
open OddLREKIdentification (sK)
open OddGrassmannSchur (sBasis)
open OddLRTableau (oddLR)
open TableauStripSigns (north directNorth northEast)

/-- `ℓ(w_λ) = NE(λ)` (E §2.2, p. 7): both count pairs of boxes, one strictly north-east of the
other. -/
theorem ell_eq_northEast (lam : YoungDiagram) : EKSemiorthogonality.ell lam = northEast lam := by
  classical
  unfold EKSemiorthogonality.ell northEast
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- `R` is diagonal in the `s^K` coordinates: `[R x]_λ = η_λ [x]_λ`. -/
theorem repr_reverse (x : Q) (lam : YoungDiagram) :
    sBasis.repr (reverseLinear x) lam = EKLSectionTwo.eta lam * sBasis.repr x lam := by
  let L₁ : Q →ₗ[ℤ] ℤ := (Finsupp.lapply lam).comp (sBasis.repr.toLinearMap.comp reverseLinear)
  let L₂ : Q →ₗ[ℤ] ℤ := EKLSectionTwo.eta lam • (Finsupp.lapply lam).comp sBasis.repr.toLinearMap
  have h : L₁ = L₂ := by
    refine sBasis.ext fun mu => ?_
    simp only [L₁, L₂, LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      Finsupp.lapply_apply, OddGrassmannSchur.sBasis_apply]
    rw [EKLSectionTwo.reverse_sK, map_zsmul, ← OddGrassmannSchur.sBasis_apply, Basis.repr_self,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases hm : mu = lam
    · subst hm; rfl
    · rw [Finsupp.single_eq_of_ne hm, mul_zero, mul_zero]
  exact LinearMap.congr_fun h x

/-- `ψ₁ψ₂` in the `s^K` coordinates: `[ψ₁ψ₂ x]_{λᵀ} = (-1)^{ℓ(w_λ)+|λ|} [x]_λ`. -/
theorem repr_psi12 (x : Q) (lam : YoungDiagram) :
    sBasis.repr (psi12 x) lam.transpose =
      (-1 : ℤ) ^ (EKSemiorthogonality.ell lam + lam.card) * sBasis.repr x lam := by
  let L₁ : Q →ₗ[ℤ] ℤ := (Finsupp.lapply lam.transpose).comp
    (sBasis.repr.toLinearMap.comp psi12.toRingHom.toIntAlgHom.toLinearMap)
  let L₂ : Q →ₗ[ℤ] ℤ := (-1 : ℤ) ^ (EKSemiorthogonality.ell lam + lam.card) •
    (Finsupp.lapply lam).comp sBasis.repr.toLinearMap
  have h : L₁ = L₂ := by
    refine sBasis.ext fun mu => ?_
    simp only [L₁, L₂, LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      Finsupp.lapply_apply, OddGrassmannSchur.sBasis_apply]
    change (sBasis.repr (psi12 (sK mu))) lam.transpose = _
    rw [OddGrassmannSchur.psi12_sK, map_zsmul, ← OddGrassmannSchur.sBasis_apply, Basis.repr_self,
      ← OddGrassmannSchur.sBasis_apply, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
      smul_eq_mul]
    by_cases hm : mu = lam
    · subst hm; simp
    · have ht : mu.transpose ≠ lam.transpose := fun he => hm (by
        rw [← YoungDiagram.transpose_transpose mu, he, YoungDiagram.transpose_transpose])
      rw [Finsupp.single_eq_of_ne ht, Finsupp.single_eq_of_ne hm, mul_zero, mul_zero]
  exact LinearMap.congr_fun h x

/-- E Definition 4.6, p. 13: `c^λ_{μν} = 0` if `|μ| + |ν| ≠ |λ|`. -/
theorem oddLR_eq_zero_of_card (lam mu nu : YoungDiagram) (h : lam.card ≠ mu.card + nu.card) :
    oddLR lam mu nu = 0 := by
  classical
  letI := DegreeShapes.degreeFintype (mu.card + nu.card)
  have hx : sK mu * sK nu ∈ EKIntegralBases.degreePiece (mu.card + nu.card) :=
    EKIntegralBases.degreePiece_mul (EKLSectionTwo.sK_mem_degree mu)
      (EKLSectionTwo.sK_mem_degree nu)
  have hexp := congrArg Subtype.val
    (EKLemma311Cond.expansion _ (EKLSectionTwo.schurOrthonormal _) ⟨_, hx⟩)
  have hmem : sK mu * sK nu ∈ Submodule.span ℤ
      {y | ∃ κ : YoungDiagram, κ.card = mu.card + nu.card ∧ y = sK κ} := by
    rw [show sK mu * sK nu = _ from hexp, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun κ _ => ?_
    rw [Submodule.coe_smul, EKLSectionTwo.schur_eq_sK]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ.val, κ.property, rfl⟩)
  exact (OddGrassmannSchur.mem_span_sK_iff _ _).mp hmem lam h

theorem eta_mul_self (lam : YoungDiagram) : EKLSectionTwo.eta lam * EKLSectionTwo.eta lam = 1 :=
  EKLSectionTwo.eta_sq lam

/-- `η_λ c^λ_{μν} = η_μ η_ν c^λ_{νμ}`. -/
theorem eta_oddLR (lam mu nu : YoungDiagram) :
    EKLSectionTwo.eta lam * oddLR lam mu nu =
      EKLSectionTwo.eta mu * EKLSectionTwo.eta nu * oddLR lam nu mu := by
  have h := repr_reverse (sK mu * sK nu) lam
  rw [EKAutomorphisms.reverse_mul, EKLSectionTwo.reverse_sK, EKLSectionTwo.reverse_sK,
    smul_mul_smul_comm, map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h
  unfold oddLR
  rw [← h, mul_comm (EKLSectionTwo.eta nu)]

/-- E Remark 4.10, (4.10), first line, p. 15:
`c^λ_{μν} = (-1)^{dN(μ)+dN(ν)+dN(λ)+N(μ)+N(ν)+N(λ)} c^λ_{νμ}`. -/
theorem remark_4_10_reverse (lam mu nu : YoungDiagram) :
    oddLR lam mu nu = (-1 : ℤ) ^ (directNorth mu + directNorth nu + directNorth lam +
      north mu + north nu + north lam) * oddLR lam nu mu := by
  have h := congrArg (fun z => EKLSectionTwo.eta lam * z) (eta_oddLR lam mu nu)
  simp only [← mul_assoc, eta_mul_self, one_mul] at h
  rw [h]
  simp only [eta_eq_directNorth_north, pow_add]
  ring

/-- E Remark 4.10, (4.10), second line, p. 15:
`c^λ_{μν} = (-1)^{NE(μ)+NE(ν)+NE(λ)} c^{λᵀ}_{μᵀνᵀ}`. -/
theorem remark_4_10_transpose (lam mu nu : YoungDiagram) :
    oddLR lam mu nu = (-1 : ℤ) ^ (northEast mu + northEast nu + northEast lam) *
      oddLR lam.transpose mu.transpose nu.transpose := by
  by_cases hc : lam.card = mu.card + nu.card
  · have h := repr_psi12 (sK mu * sK nu) lam
    rw [map_mul, OddGrassmannSchur.psi12_sK, OddGrassmannSchur.psi12_sK, smul_mul_smul_comm,
      map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h
    change _ * oddLR lam.transpose mu.transpose nu.transpose = _ * oddLR lam mu nu at h
    have hsq : ∀ a : ℕ, ((-1 : ℤ) ^ a) ^ 2 = 1 := fun a => by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hC := hsq (EKSemiorthogonality.ell lam + lam.card)
    have hu := hsq mu.card
    have hv := hsq nu.card
    rw [hc] at h hC
    simp only [ell_eq_northEast, pow_add] at h hC ⊢
    linear_combination (-((-1 : ℤ) ^ northEast lam * (-1) ^ mu.card * (-1) ^ nu.card)) * h -
      oddLR lam mu nu * hC +
      ((-1 : ℤ) ^ northEast lam * (-1) ^ northEast mu * (-1) ^ northEast nu *
        oddLR lam.transpose mu.transpose nu.transpose * ((-1) ^ nu.card) ^ 2) * hu +
      ((-1 : ℤ) ^ northEast lam * (-1) ^ northEast mu * (-1) ^ northEast nu *
        oddLR lam.transpose mu.transpose nu.transpose) * hv
  · rw [oddLR_eq_zero_of_card _ _ _ hc, oddLR_eq_zero_of_card, mul_zero]
    simpa [EKLSectionTwo.card_transpose] using hc

/-- E Remark 4.10, p. 15: if `c^λ_{μμ} ≠ 0` then `(-1)^{dN(λ)+N(λ)} = 1`. -/
theorem remark_4_10_square (lam mu : YoungDiagram) (h : oddLR lam mu mu ≠ 0) :
    (-1 : ℤ) ^ (directNorth lam + north lam) = 1 := by
  have he := eta_oddLR lam mu mu
  rw [eta_mul_self, one_mul] at he
  rw [← eta_eq_directNorth_north]
  have h1 : (EKLSectionTwo.eta lam - 1) * oddLR lam mu mu = 0 := by rw [sub_mul, he]; ring
  rcases mul_eq_zero.mp h1 with h2 | h2
  · linarith
  · exact absurd h2 h

end OddMath.Frontier.OddLRMisc
