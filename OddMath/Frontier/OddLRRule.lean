import OddMath.Frontier.OddLRRuleCount

/-!
# The odd Littlewood–Richardson rule

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1, Theorem 4.8, display (4.6), p.14:
for all partitions `λ, μ, ν`, the odd Littlewood–Richardson coefficient (E Definition 4.6,
`OddLRTableau.oddLR`) is
`c^λ_{μν} = (-1)^{N(μ)+N(λ)} Σ_{S ∈ SSYT(λ/μ, ν), w_r(S) Yamanouchi} (-1)^{N^<(S)}`
(`thm_4_8`).

Route. The paper derives (4.6) from Lemma 4.7, which reads `c^λ_{μν}` off the odd plactic ring
and so rests on Corollary 3.9. Here Corollary 3.9 is not used:
1. `skew_pieri`: iterating the odd horizontal Pieri rule gives
   `s_μ h_β = Σ_λ (-1)^{N(μ)+N(λ)} (Σ_{S ∈ SSYT(λ/μ,β)} (-1)^{N^<(Ŝ)}) s_λ`;
2. `skew_kostka_lr`: the RSK form of the Littlewood–Richardson correspondence of E's proof
   (with the odd RSK sign, EK Thm 3.7) gives
   `Σ_{S ∈ SSYT(λ/μ,β)} (-1)^{N^<(Ŝ)} = Σ_ν (Σ_{S ∈ LR(λ/μ,ν)} (-1)^{N^<(Ŝ)}) K_{νβ}`;
3. `h_β = Σ_ν K_{νβ} s_ν` (E (2.7)) and invertibility of the odd Kostka matrix give (4.6).
-/

namespace OddMath.Frontier.OddLRRule

open TableauSign TableauContent OddLRTableau DegreeShapes CompleteTableauExpansion
open EKRadicalQuotient (Q)
open OddLREKIdentification (sK)
open scoped BigOperators

attribute [local instance] Classical.propDecidable degreeFintype

/-- E (2.7): `h_β = Σ_ν K_{νβ} s_ν`. -/
theorem hPartition_expand (d : ℕ) (β : DegreeShape d) :
    EKPartitionSpanning.hPartition β.val =
      ∑ ν : DegreeShape d, TableauDominance.signedKostka ν.val β.val • sK ν.val := by
  rw [EKOddRSKII.schur_defining]
  apply Finset.sum_congr rfl
  intro ν _
  rw [OddSymmetricLimit.sK_eq]
  rfl

/-- The row lengths of `β`, one-based. -/
def rowC (β : YoungDiagram) (i : ℕ) : ℕ := β.rowLen (i - 1)

theorem hPartition_eq_prod (β : YoungDiagram) :
    EKPartitionSpanning.hPartition β =
      ((List.range (β.colLen 0)).map (fun i => EKElementaryQuotient.h (rowC β (i + 1)))).prod := by
  unfold EKPartitionSpanning.hPartition YoungDiagram.rowLens rowC
  simp [List.map_map, Function.comp_def]

theorem prefixContent_rowC (β : YoungDiagram) :
    prefixContent (rowC β) (β.colLen 0) = TableauDominance.shapeContent β := by
  ext k
  rcases k with _ | i
  · simp [TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply]
  · rw [prefixContent_apply_succ, shapeContent_succ]
    split_ifs with h
    · rfl
    · rw [rowLen_eq_zero (by omega)]

theorem mdeg_rowC (mu β : YoungDiagram) : mdeg mu (rowC β) (β.colLen 0) = mu.card + β.card := by
  unfold mdeg
  congr 1
  rw [← prefixContent_total, prefixContent_rowC, ← TableauDominance.content_canonical, content_total]

/-- `s_μ h_β` in the Schur basis (skew signed Kostka numbers). -/
theorem sK_mul_hPartition (mu β : YoungDiagram) :
    sK mu * EKPartitionSpanning.hPartition β = ∑ lam : DegreeShape (mu.card + β.card),
      ((-1 : ℤ) ^ (TableauStripSigns.north mu + TableauStripSigns.north lam.val) *
        ∑ S ∈ ofContent lam.val mu (TableauDominance.shapeContent β), S.sign) • sK lam.val := by
  rw [hPartition_eq_prod, skew_pieri, prefixContent_rowC]
  exact sum_degreeShape_congr (mdeg_rowC mu β) (fun lam => ((-1 : ℤ) ^ (TableauStripSigns.north mu +
    TableauStripSigns.north lam) * ∑ S ∈ ofContent lam mu (TableauDominance.shapeContent β),
      S.sign) • sK lam)

theorem lrTableaux_eq_empty {lam mu nu : YoungDiagram} (h : lam.card ≠ mu.card + nu.card) :
    lrTableaux lam mu nu = ∅ := by
  apply Finset.eq_empty_of_forall_not_mem
  intro S hS
  obtain ⟨hc, -⟩ := mem_lrTableaux.mp hS
  apply h
  have h1 : (S.content).sum (fun _ n => n) = (skewCells lam mu).card := by
    classical
    rw [SkewTableau.content, ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simp only [Finsupp.sum_single_index (h := fun _ n : ℕ => n) rfl, Finset.sum_const, smul_eq_mul,
      mul_one]
  rw [hc, ← TableauDominance.content_canonical, content_total] at h1
  have h2 : (skewCells lam mu).card = lam.card - mu.card := by
    unfold skewCells
    rw [Finset.card_sdiff (YoungDiagram.cells_subset_iff.mpr S.sub)]
  have h3 : mu.card ≤ lam.card := Finset.card_le_card (YoungDiagram.cells_subset_iff.mpr S.sub)
  omega

theorem lrSignedCount_eq_zero {lam mu nu : YoungDiagram} (h : lam.card ≠ mu.card + nu.card) :
    lrSignedCount lam mu nu = 0 := by
  rw [lrSignedCount, lrTableaux_eq_empty h, Finset.sum_empty, mul_zero]

/-- The product `s_μ s_ν` expanded by the odd Littlewood–Richardson rule. -/
theorem sK_mul_sK (mu nu : YoungDiagram) :
    sK mu * sK nu = ∑ lam : DegreeShape (mu.card + nu.card), lrSignedCount lam.val mu nu • sK lam.val := by
  set d := nu.card
  let F : DegreeShape d → Q := fun ν =>
    ∑ lam : DegreeShape (mu.card + d), lrSignedCount lam.val mu ν.val • sK lam.val
  let G : DegreeShape d → Q := fun ν => sK mu * sK ν.val
  have hG : KostkaModuleInversion.transform d G =
      fun β => sK mu * EKPartitionSpanning.hPartition β.val := by
    funext β
    change ∑ ν : DegreeShape d, TableauDominance.signedKostka ν.val β.val • (sK mu * sK ν.val) = _
    rw [hPartition_expand d β, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    rw [mul_smul_comm]
  have hF : KostkaModuleInversion.transform d F =
      fun β => sK mu * EKPartitionSpanning.hPartition β.val := by
    funext β
    change ∑ ν : DegreeShape d, TableauDominance.signedKostka ν.val β.val •
      (∑ lam : DegreeShape (mu.card + d), lrSignedCount lam.val mu ν.val • sK lam.val) = _
    rw [sK_mul_hPartition, β.property]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro lam _
    rw [← Finset.sum_smul]
    congr 1
    have hk := skew_kostka_lr lam.val mu β.val
    rw [β.property] at hk
    rw [hk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    unfold lrSignedCount
    ring
  have hu := (KostkaModuleInversion.uniqueSolution d
    (fun β : DegreeShape d => sK mu * EKPartitionSpanning.hPartition β.val)).unique hG hF
  exact congrFun hu ⟨nu, rfl⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- **E Theorem 4.8 (4.6), the odd Littlewood–Richardson rule**: for all partitions
`λ, μ, ν`, `c^λ_{μν} = (-1)^{N(μ)+N(λ)} Σ_{S LR tableau of shape λ/μ and content ν} (-1)^{N^<(S)}`. -/
theorem thm_4_8 (lam mu nu : YoungDiagram) : oddLR lam mu nu = lrSignedCount lam mu nu := by
  unfold oddLR
  rw [sK_mul_sK, map_sum]
  simp_rw [map_zsmul, ← OddGrassmannSchur.sBasis_apply, Basis.repr_self, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases h : lam.card = mu.card + nu.card
  · rw [Fintype.sum_eq_single (α := DegreeShape (mu.card + nu.card)) ⟨lam, h⟩ ?_]
    · simp
    · intro x hx
      rw [if_neg (fun h' => hx (Subtype.ext h'))]
  · rw [lrSignedCount_eq_zero h]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    intro h'
    exact h (h' ▸ x.property)

end OddMath.Frontier.OddLRRule
