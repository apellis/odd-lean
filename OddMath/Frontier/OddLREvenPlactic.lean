import OddMath.Frontier.OddLREvenRule
import OddMath.Frontier.OddLRRuleLemma47

/-!
# E (4.2): the even Littlewood–Richardson coefficient as a count of plactic factorizations

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §4.1, display (4.2), p.12:
`c^λ_{μν} = #{U ∈ SSYT(μ) : U T_ν = T_λ}`, the product taken in the (even) plactic monoid
(Knuth equivalence of row words; `OddLRRule.lemma47Set`). This is `evenLR_eq_card_lemma47Set`,
from Theorem 4.1 (`OddLREven.thm_4_1`) and the Littlewood–Richardson correspondence of E's proof
of Theorem 4.8 (`card_lemma47Set`: the bijection of `OddLRRule.sum_keys_lemma47` without signs).
-/

namespace OddMath.Frontier.OddLREven

open scoped BigOperators
open TableauSign TableauEvaluation TableauContent OddLRTableau EKClassicalPlactic DegreeShapes
open OddLRRule
open EKRskBijection (Pairs Tab rskRec)

noncomputable section

attribute [local instance] Classical.propDecidable

variable {lam mu : YoungDiagram}

/-- `#{U ∈ SSYT(μ) : U T_ν = T_λ}` is the number of keys `(U-block, T_ν)` of the
Littlewood–Richardson correspondence. -/
theorem card_lemma47Set (nu : YoungDiagram) :
    (lemma47Set lam mu nu).card = ((keys lam mu nu.card).filter (fun k => k.2.1 = nu)).card := by
  apply Finset.card_bij (fun U hU => (umatOf lam mu U (inAlphabet_of_mem hU),
    (⟨nu, TableauDominance.canonicalTableau nu⟩ : Σ ν : YoungDiagram, PositiveTableau ν)))
  · intro U hU
    let V := (rskE (lam.colLen 0) nu.card).symm ⟨nu,
      ⟨TableauDominance.canonicalTableau nu, canonical_inAlphabet_of_mem hU⟩,
      ⟨TableauDominance.canonicalTableau nu, canonical_inAlphabet_card nu⟩⟩
    have hV : rskRec _ nu.card V = ⟨nu,
        ⟨TableauDominance.canonicalTableau nu, canonical_inAlphabet_of_mem hU⟩,
        ⟨TableauDominance.canonicalTableau nu, canonical_inAlphabet_card nu⟩⟩ :=
      (rskE _ _).apply_symm_apply _
    have hPV : P (colword V) = P (readR (nrows (TableauDominance.canonicalTableau nu))) := by
      rw [← nrows_rskP, hV, P_readR _ (nrows_valid _)]
    obtain ⟨S, hSU, hSV⟩ := exists_of_blocks (r := nu.card) (umatOf lam mu U (inAlphabet_of_mem hU))
      (by rw [rsk_umatOf])
      (by intro p hp; rw [rsk_umatOf]; exact TableauDominance.canonical_entry hp) V
      (by
        rw [rskRec_join, nrows_rskFrom, rsk_umatOf]
        change insW (nrows U) (colword V) = _
        rw [insW_congr (nrows_valid U) hPV, insW_readR _ (nrows_valid U), ← rowWord_eq_readR_nrows,
          ← rowWord_eq_readR_nrows, P_eq_of_knuth (mem_lemma47Set.mp hU), P_rowWord])
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨S, Finset.mem_univ _, ?_⟩, rfl⟩
    rw [show key S = (matU S, ⟨(zV S).1, (zV S).2.1.1⟩) from rfl, hSU,
      show zV S = rskRec _ nu.card (matV S) from rfl, hSV, hV]
  · intro U hU U' hU' h
    have h1 := congrArg (fun k => rskRec (lam.colLen 0) (mu.colLen 0) k.1) h
    simp only [rsk_umatOf, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, Subtype.mk.injEq,
      true_and] at h1
    exact h1.1
  · intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
    obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hk1
    change (zV S).1 = nu at hk2
    have hj := rskRec_join (matU S) nu.card (matV S)
    rw [join_UV S, rsk_matA] at hj
    have hPpart := congrArg (fun z => nrows z.2.1.1) hj
    simp only [nrows_rskFrom] at hPpart
    change nrows (TableauDominance.canonicalTableau lam) = _ at hPpart
    have hPV : P (colword (matV S)) = P (readR (nrows (zV S).2.1.1)) := by
      rw [← nrows_rskP, P_readR _ (nrows_valid _)]; rfl
    rw [insW_congr (nrows_valid _) hPV, insW_readR _ (nrows_valid _)] at hPpart
    have hcan := eq_canonical_of_product _ _ hPpart.symm
    obtain ⟨hz0, hz0e⟩ := rskU_shape S
    have hkey : key S = (matU S, ⟨nu, TableauDominance.canonicalTableau nu⟩) := by
      rw [show key S = (matU S, ⟨(zV S).1, (zV S).2.1.1⟩) from rfl]
      congr 1
      rw [hcan, hk2]
    rw [hcan] at hPpart
    generalize hz : rskRec (lam.colLen 0) (mu.colLen 0) (matU S) = z0 at hz0 hz0e hPpart
    obtain ⟨mu', ⟨PU, hPU⟩, ⟨QU, hQU⟩⟩ := z0
    dsimp only at hz0 hz0e hPpart
    subst hz0
    have hQ : QU = TableauDominance.canonicalTableau mu' := by
      apply ext_cells
      intro p hp
      rw [hz0e p hp, TableauDominance.canonical_entry hp]
    subst hQ
    generalize (zV S).1 = ν' at hPpart hk2
    subst hk2
    have hmem : PU ∈ lemma47Set lam mu' ν' := by
      rw [mem_lemma47Set]
      apply knuth_of_P_eq
      rw [rowWord_eq_readR_nrows PU, rowWord_eq_readR_nrows (TableauDominance.canonicalTableau ν'),
        ← hPpart, P_rowWord]
    refine ⟨PU, hmem, ?_⟩
    rw [hkey]
    congr 1
    apply (rskE _ _).injective
    change rskRec _ _ (umatOf lam mu' PU _) = rskRec _ _ (matU S)
    rw [rsk_umatOf, hz]

/-- `#{U ∈ SSYT(μ) : U T_ν = T_λ} = #LR(λ/μ, ν)`. -/
theorem card_lemma47Set_eq (lam mu nu : YoungDiagram) :
    (lemma47Set lam mu nu).card = (lrTableaux lam mu nu).card := by
  rw [card_lemma47Set, card_lr nu le_rfl]

/-- **E (4.2)**: `c^λ_{μν} = #{U ∈ SSYT(μ) : U T_ν = T_λ}`, the product `U T_ν` taken in the even
plactic monoid. -/
theorem evenLR_eq_card_lemma47Set (lam mu nu : YoungDiagram) :
    evenLR lam mu nu = (lemma47Set lam mu nu).card := by
  rw [thm_4_1, card_lemma47Set_eq]

end

end OddMath.Frontier.OddLREven
