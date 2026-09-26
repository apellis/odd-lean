import OddMath.Frontier.OddLRRuleBijection

/-!
# Skew signed Kostka numbers in terms of Littlewood–Richardson tableaux

`Σ_{S ∈ SSYT(λ/μ, β)} (-1)^{N^<(Ŝ)} = Σ_ν (Σ_{S LR of shape λ/μ, content ν} (-1)^{N^<(Ŝ)}) K_{νβ}`
(`skew_kostka_lr`), where `K` is the odd Kostka number (E (2.6),
`TableauDominance.signedKostka`). This is the signed form of the Littlewood–Richardson
correspondence of Ellis, arXiv:1111.3932v1, proof of Theorem 4.8, pp.14–15, obtained from
`OddLRRule.key_inj`, `key_replace`, `sign_eq_kappa` and `isLR_iff_QV`.
-/

namespace OddMath.Frontier.OddLRRule

open TableauSign TableauEvaluation TableauContent OddLRTableau DegreeShapes
open scoped BigOperators

attribute [local instance] Classical.propDecidable degreeFintype

variable {lam mu : YoungDiagram} {r : ℕ}

/-- Encoding of a bounded skew tableau by its entries on `λ/μ`. -/
def skEncode (S : SkR lam mu r) : skewCells lam mu → Fin (r + 1) :=
  fun p => ⟨S.1.entry p.1.1 p.1.2, Nat.lt_succ_of_le (S.2 _ _)⟩

theorem skEncode_injective : Function.Injective (skEncode (lam := lam) (mu := mu) (r := r)) := by
  intro S S' h
  apply Subtype.ext
  apply SkewTableau.ext_skew
  intro p hp
  have := congrArg (fun f => (f ⟨p, hp⟩ : ℕ)) h
  simpa [skEncode] using this

noncomputable instance : Fintype (SkR lam mu r) := Fintype.ofInjective _ skEncode_injective

theorem entry_le_of_content (S : SkewTableau lam mu) {c : ℕ →₀ ℕ} (hS : S.content = c)
    (hc : ∀ k ∈ c.support, k ≤ r) : ∀ i j, S.entry i j ≤ r := by
  intro i j
  by_cases h : (i, j) ∈ skewCells lam mu
  · have := S.entry_mem_support h
    rw [hS] at this
    exact hc _ this
  · rcases (show (i, j) ∉ lam ∨ (i, j) ∈ mu by rw [mem_skewCells] at h; tauto) with hl | hm
    · rw [S.zeros_out hl]; omega
    · rw [S.zeros_in hm]; omega

theorem inAlphabet_of_content {ν : YoungDiagram} (T : PositiveTableau ν) {c : ℕ →₀ ℕ}
    (hT : content T = c) (hc : ∀ k ∈ c.support, k ≤ r) : InAlphabet r T := by
  intro p hp
  have := entry_mem_support T hp
  rw [hT] at this
  exact hc _ this

/-- Bounded skew tableaux of content `c`. -/
noncomputable def cFin (c : ℕ →₀ ℕ) : Finset (SkR lam mu r) :=
  Finset.univ.filter (fun S => S.1.content = c)

theorem sum_ofContent (c : ℕ →₀ ℕ) (hc : ∀ k ∈ c.support, k ≤ r) (f : SkewTableau lam mu → ℤ) :
    ∑ S ∈ ofContent lam mu c, f S = ∑ S ∈ cFin (r := r) c, f S.1 := by
  apply Finset.sum_bij (fun S hS => (⟨S, entry_le_of_content S (mem_ofContent.mp hS) hc⟩ :
    SkR lam mu r))
  · intro S hS
    simp [cFin, mem_ofContent.mp hS]
  · intro S _ S' _ h
    exact congrArg Subtype.val h
  · intro S hS
    refine ⟨S.1, mem_ofContent.mpr (by simpa [cFin] using hS), rfl⟩
  · intro S _; rfl

variable (lam mu r) in
/-- The keys `(U, P(V))` that occur. -/
noncomputable def keys :
    Finset ((Fin (mu.colLen 0) → Fin (lam.colLen 0) → ℕ) × (Σ ν : YoungDiagram, PositiveTableau ν)) :=
  Finset.univ.image (key (lam := lam) (mu := mu) (r := r))

theorem sum_cFin (c : ℕ →₀ ℕ) (hc : ∀ k ∈ c.support, k ≤ r) :
    ∑ S ∈ cFin (lam := lam) (mu := mu) (r := r) c, S.1.sign =
      ∑ k ∈ keys lam mu r, kappa lam mu k *
        ∑ T ∈ tableauxOfContent k.2.1 c, TableauDominance.tableauSign T := by
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sigma (keys lam mu r) (fun k => tableauxOfContent k.2.1 c)
    (fun x => kappa lam mu x.1 * TableauDominance.tableauSign x.2)]
  apply Finset.sum_bij (fun S _ => (⟨key S, (zV S).2.2.1⟩ :
    Σ k : (Fin (mu.colLen 0) → Fin (lam.colLen 0) → ℕ) × (Σ ν : YoungDiagram, PositiveTableau ν),
      PositiveTableau k.2.1))
  · intro S hS
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    rw [mem_tableauxOfContent]
    change content (zV S).2.2.1 = c
    rw [content_QV]
    simpa [cFin] using hS
  · intro S _ S' _ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨hk, hq⟩ := h
    apply key_inj hk
    unfold QV
    exact Sigma.ext (congrArg (fun k => k.2.1) hk) hq
  · rintro ⟨k, T⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hk, hT⟩ := hx
    obtain ⟨S0, -, rfl⟩ := Finset.mem_image.mp hk
    rw [mem_tableauxOfContent] at hT
    obtain ⟨S', hk', hq'⟩ := key_replace S0 T (inAlphabet_of_content T hT hc)
    refine ⟨S', ?_, ?_⟩
    · simp only [cFin, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← content_QV]
      have := congrArg (fun x : Σ ν : YoungDiagram, PositiveTableau ν => content x.2) hq'
      simp only [QV] at this
      rw [this]; exact hT
    · unfold QV at hq'
      exact Sigma.ext hk' (Sigma.mk.inj hq').2
  · intro S _
    exact sign_eq_kappa S

theorem sum_lr (ν : YoungDiagram) (hr : ν.card ≤ r) :
    ∑ S ∈ lrTableaux lam mu ν, S.sign =
      ∑ k ∈ (keys lam mu r).filter (fun k => k.2.1 = ν),
        kappa lam mu k * TableauDominance.tableauSign (TableauDominance.canonicalTableau ν) := by
  have hc : ∀ k ∈ (TableauDominance.shapeContent ν).support, k ≤ r := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk
    rcases k with _ | i
    · omega
    · rw [shapeContent_succ] at hk
      have h1 : (i, 0) ∈ ν := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hk)
      have h2 : i < ν.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp h1
      have h3 : ν.colLen 0 ≤ ν.card := by
        have : (Finset.range (ν.colLen 0)).image (fun i => (i, 0)) ⊆ ν.cells := by
          intro p hp
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
          simpa using YoungDiagram.mem_iff_lt_colLen.mpr (Finset.mem_range.mp hi)
        have := Finset.card_le_card this
        rwa [Finset.card_image_of_injective _ (fun a b h => by simpa using h),
          Finset.card_range] at this
      omega
  have hlr : lrTableaux lam mu ν = (ofContent lam mu (TableauDominance.shapeContent ν)).filter IsLR := by
    ext S; rw [mem_lrTableaux, Finset.mem_filter, mem_ofContent]
  rw [hlr, Finset.sum_filter, sum_ofContent _ hc, ← Finset.sum_filter]
  apply Finset.sum_bij (fun S _ => key S)
  · intro S hS
    simp only [Finset.mem_filter, cFin, Finset.mem_univ, true_and] at hS
    refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have := (isLR_iff_QV S ν hS.1).mp hS.2
    exact congrArg Sigma.fst this
  · intro S hS S' hS' h
    simp only [Finset.mem_filter, cFin, Finset.mem_univ, true_and] at hS hS'
    exact key_inj h (((isLR_iff_QV S ν hS.1).mp hS.2).trans ((isLR_iff_QV S' ν hS'.1).mp hS'.2).symm)
  · intro k hk
    obtain ⟨hk, hν⟩ := Finset.mem_filter.mp hk
    obtain ⟨S0, -, rfl⟩ := Finset.mem_image.mp hk
    change (zV S0).1 = ν at hν
    subst hν
    obtain ⟨S', hk', hq'⟩ := key_replace S0 (TableauDominance.canonicalTableau (zV S0).1)
      (inAlphabet_of_content _ (TableauDominance.content_canonical _) hc)
    have hcont : S'.1.content = TableauDominance.shapeContent (zV S0).1 := by
      rw [← content_QV]
      have := congrArg (fun x : Σ ν : YoungDiagram, PositiveTableau ν => content x.2) hq'
      simp only [QV] at this
      rw [this, TableauDominance.content_canonical]
    refine ⟨S', ?_, hk'⟩
    simp only [Finset.mem_filter, cFin, Finset.mem_univ, true_and]
    exact ⟨hcont, (isLR_iff_QV S' _ hcont).mpr hq'⟩
  · intro S hS
    simp only [Finset.mem_filter, cFin, Finset.mem_univ, true_and] at hS
    have hq := (isLR_iff_QV S ν hS.1).mp hS.2
    rw [sign_eq_kappa]
    congr 1
    unfold QV at hq
    exact tableauSign_congr hq

theorem shapeContent_le_card (ν : YoungDiagram) :
    ∀ k ∈ (TableauDominance.shapeContent ν).support, k ≤ ν.card := by
  intro k hk
  rw [Finsupp.mem_support_iff] at hk
  rcases k with _ | i
  · omega
  · rw [shapeContent_succ] at hk
    have h1 : (i, 0) ∈ ν := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hk)
    have h2 : i < ν.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp h1
    have : (Finset.range (ν.colLen 0)).image (fun i => (i, 0)) ⊆ ν.cells := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      simpa using YoungDiagram.mem_iff_lt_colLen.mpr (Finset.mem_range.mp hi)
    have := Finset.card_le_card this
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range] at this
    change i + 1 ≤ ν.cells.card
    omega

theorem signedKostka_eq_zero_of_card {ν β : YoungDiagram} (h : ν.card ≠ β.card) :
    TableauDominance.signedKostka ν β = 0 := by
  unfold TableauDominance.signedKostka
  rw [Finset.sum_eq_zero, mul_zero]
  intro T hT
  rw [mem_tableauxOfContent] at hT
  have := content_total T
  rw [hT, ← TableauDominance.content_canonical, content_total] at this
  exact absurd this.symm h

theorem sum_sign_fiber (ν β : YoungDiagram) :
    ∑ T ∈ tableauxOfContent ν (TableauDominance.shapeContent β), TableauDominance.tableauSign T =
      TableauDominance.tableauSign (TableauDominance.canonicalTableau ν) *
        TableauDominance.signedKostka ν β := by
  unfold TableauDominance.signedKostka
  rw [← mul_assoc, TableauDominance.tableauSign_mul_self, one_mul]

/-- **Signed Littlewood–Richardson correspondence**:
`Σ_{S ∈ SSYT(λ/μ, β)} (-1)^{N^<(Ŝ)} = Σ_ν (Σ_{S ∈ LR(λ/μ, ν)} (-1)^{N^<(Ŝ)}) K_{νβ}`. -/
theorem skew_kostka_lr (lam mu β : YoungDiagram) :
    ∑ S ∈ ofContent lam mu (TableauDominance.shapeContent β), S.sign =
      ∑ ν : DegreeShape β.card,
        (∑ S ∈ lrTableaux lam mu ν.val, S.sign) * TableauDominance.signedKostka ν.val β := by
  rw [sum_ofContent (r := β.card) _ (shapeContent_le_card β), sum_cFin _ (shapeContent_le_card β)]
  have hlr : ∀ ν : DegreeShape β.card, ∑ S ∈ lrTableaux lam mu ν.val, S.sign =
      ∑ k ∈ (keys lam mu β.card).filter (fun k => k.2.1 = ν.val),
        kappa lam mu k * TableauDominance.tableauSign (TableauDominance.canonicalTableau ν.val) :=
    fun ν => sum_lr ν.val (le_of_eq ν.property)
  simp_rw [hlr, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_sign_fiber]
  have hg : ∀ ν : DegreeShape β.card,
      (if k.2.1 = ν.val then kappa lam mu k *
        TableauDominance.tableauSign (TableauDominance.canonicalTableau ν.val) *
          TableauDominance.signedKostka ν.val β else 0) =
      if k.2.1 = ν.val then kappa lam mu k *
        TableauDominance.tableauSign (TableauDominance.canonicalTableau k.2.1) *
          TableauDominance.signedKostka k.2.1 β else 0 := by
    intro ν
    split_ifs with h
    · rw [h]
    · rfl
  simp_rw [hg]
  by_cases hd : k.2.1.card = β.card
  · rw [Fintype.sum_eq_single (α := DegreeShape β.card) ⟨k.2.1, hd⟩ ?_]
    · rw [if_pos rfl, mul_assoc]
    · intro ν hν
      rw [if_neg (fun h => hν (Subtype.ext h.symm))]
  · rw [signedKostka_eq_zero_of_card hd, mul_zero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro ν _
    split_ifs with h
    · rw [mul_zero]
    · rfl

end OddMath.Frontier.OddLRRule
