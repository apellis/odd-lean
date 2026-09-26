import OddMath.Frontier.OddLREvenSchur

/-!
# The even Littlewood–Richardson rule

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §4.1, Theorem 4.1, p.12
(Fulton, *Young Tableaux*, §5.2, Prop. 3): for all partitions `λ, μ, ν`, the coefficient
`c^λ_{μν}` of `s_λ` in `s_μ s_ν` (in the ring of symmetric functions `Λ₁`,
`OddLREven.evenLR`) equals the number of Littlewood–Richardson tableaux of shape `λ/μ` and
content `ν` (`thm_4_1`).

The proof is the proof of the odd rule (`OddLRRule.thm_4_8`) with the signs dropped:
1. `skew_pieri0`: iterating the even Pieri rule (`OddLREven.sE_mul_hk`) along the strips of
   `T_S` gives `s_μ h_β = Σ_λ #SSYT(λ/μ, β) s_λ`;
2. `skew_kostka_lr0`: the RSK form of the Littlewood–Richardson correspondence
   (`OddLRRule.key_inj`, `key_replace`, `isLR_iff_QV`) gives
   `#SSYT(λ/μ, β) = Σ_ν #LR(λ/μ, ν) K_{νβ}`;
3. `h_β = Σ_ν K_{νβ} s_ν` and invertibility of the Kostka matrix.
-/

namespace OddMath.Frontier.OddLREven

open scoped BigOperators
open DegreeShapes TableauSign TableauContent OddLRTableau OddLRRule CompleteTableauExpansion
open TableauStripCorners

noncomputable section

attribute [local instance] degreeFintype Classical.propDecidable

/-! ## Iterated even Pieri rule -/

theorem pieri_iter0 (mu : YoungDiagram) (c : ℕ → ℕ) (t : ℕ) :
    sE mu * ((List.range t).map (fun i => hk (c (i + 1)))).prod =
      ∑ lam : DegreeShape (mdeg mu c t), (W0 mu c t lam.val : ℤ) • sE lam.val := by
  induction t with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil, mul_one]
    have hd : mdeg mu c 0 = mu.card := by simp [mdeg, prefixDegree]
    symm
    rw [Fintype.sum_eq_single (α := DegreeShape (mdeg mu c 0)) ⟨mu, hd.symm⟩ ?_]
    · rw [W0_zero, if_pos rfl]; simp
    · intro b hb
      rw [W0_zero, if_neg (fun h => hb (Subtype.ext h))]; simp
  | succ t ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      ← mul_assoc, ih, Finset.sum_mul]
    simp_rw [smul_mul_assoc]
    have hstep : ∀ u : DegreeShape (mdeg mu c t),
        sE u.val * hk (c (t + 1)) = ∑ w : DegreeShape (mdeg mu c (t + 1)),
          if Horizontal u.val w.val then sE w.val else 0 := fun u => by
      rw [sE_mul_hk (mdeg mu c t) (c (t + 1)) u]
      exact sum_degreeShape_eq (by rw [mdeg, mdeg, prefixDegree_succ]; ring)
        (fun w => if Horizontal u.val w then sE w else 0)
    simp_rw [hstep, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [W0_succ, Nat.cast_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp

theorem hE_eq_prod (β : YoungDiagram) :
    hE β = ((List.range (β.colLen 0)).map (fun i => hk (rowC β (i + 1)))).prod := by
  unfold hE EKGeneralQ.hWord YoungDiagram.rowLens
  rw [map_list_prod]
  simp [List.map_map, Function.comp_def, hk, rowC]

/-- **Skew even Pieri expansion**: `s_μ h_β = Σ_λ #SSYT(λ/μ, β) s_λ` in `Λ₁`. -/
theorem skew_pieri0 (mu β : YoungDiagram) :
    sE mu * hE β = ∑ lam : DegreeShape (mu.card + β.card),
      ((ofContent lam.val mu (TableauDominance.shapeContent β)).card : ℤ) • sE lam.val := by
  rw [hE_eq_prod, pieri_iter0]
  simp_rw [W0_eq, prefixContent_rowC]
  exact sum_degreeShape_eq (mdeg_rowC mu β) (fun lam =>
    ((ofContent lam mu (TableauDominance.shapeContent β)).card : ℤ) • sE lam)

/-! ## The unsigned Littlewood–Richardson correspondence -/

section Count

variable {lam mu : YoungDiagram} {r : ℕ}

theorem card_cFin (c : ℕ →₀ ℕ) (hc : ∀ k ∈ c.support, k ≤ r) :
    (cFin (lam := lam) (mu := mu) (r := r) c).card =
      ∑ k ∈ keys lam mu r, (tableauxOfContent k.2.1 c).card := by
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun S _ => (⟨key S, (zV S).2.2.1⟩ :
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

theorem card_ofContent_eq (c : ℕ →₀ ℕ) (hc : ∀ k ∈ c.support, k ≤ r) (P : SkewTableau lam mu → Prop) :
    ((ofContent lam mu c).filter P).card = ((cFin (r := r) c).filter (fun S => P S.1)).card := by
  have := sum_ofContent (r := r) c hc (fun S => if P S then (1 : ℤ) else 0)
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_inj] at this
  exact this

theorem card_lr (ν : YoungDiagram) (hr : ν.card ≤ r) :
    (lrTableaux lam mu ν).card = ((keys lam mu r).filter (fun k => k.2.1 = ν)).card := by
  have hc : ∀ k ∈ (TableauDominance.shapeContent ν).support, k ≤ r :=
    fun k hk => le_trans (shapeContent_le_card ν k hk) hr
  have hlr : lrTableaux lam mu ν = (ofContent lam mu (TableauDominance.shapeContent ν)).filter IsLR := by
    ext S; rw [mem_lrTableaux, Finset.mem_filter, mem_ofContent]
  rw [hlr, card_ofContent_eq _ hc]
  apply Finset.card_bij (fun S _ => key S)
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

theorem tableauxOfContent_eq_empty {ν β : YoungDiagram} (h : ν.card ≠ β.card) :
    tableauxOfContent ν (TableauDominance.shapeContent β) = ∅ := by
  apply Finset.eq_empty_of_forall_not_mem
  intro T hT
  rw [mem_tableauxOfContent] at hT
  have := content_total T
  rw [hT, ← TableauDominance.content_canonical, content_total] at this
  exact h this.symm

/-- **Unsigned Littlewood–Richardson correspondence**:
`#SSYT(λ/μ, β) = Σ_{ν ⊢ |β|} #LR(λ/μ, ν) · K_{νβ}`. -/
theorem skew_kostka_lr0 (lam mu β : YoungDiagram) :
    (ofContent lam mu (TableauDominance.shapeContent β)).card =
      ∑ ν : DegreeShape β.card, (lrTableaux lam mu ν.val).card *
        (tableauxOfContent ν.val (TableauDominance.shapeContent β)).card := by
  have hc := shapeContent_le_card β
  have e0 := card_ofContent_eq (lam := lam) (mu := mu) (r := β.card) _ hc (fun _ => True)
  simp only [Finset.filter_True] at e0
  rw [e0, card_cFin _ hc]
  have hlr : ∀ ν : DegreeShape β.card, (lrTableaux lam mu ν.val).card =
      ((keys lam mu β.card).filter (fun k => k.2.1 = ν.val)).card :=
    fun ν => card_lr ν.val (le_of_eq ν.property)
  simp_rw [hlr, Finset.card_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hd : k.2.1.card = β.card
  · rw [Fintype.sum_eq_single (α := DegreeShape β.card) ⟨k.2.1, hd⟩ ?_]
    · simp
    · intro ν hν
      rw [if_neg (fun h => hν (Subtype.ext h.symm)), zero_mul]
  · rw [tableauxOfContent_eq_empty hd, Finset.card_empty]
    symm
    apply Finset.sum_eq_zero
    intro ν _
    split_ifs with h
    · rw [← h, tableauxOfContent_eq_empty hd, Finset.card_empty, mul_zero]
    · rw [zero_mul]

end Count

/-! ## The even Littlewood–Richardson rule -/

/-- The product `s_μ s_ν` expanded by the even Littlewood–Richardson rule. -/
theorem sE_mul_sE (mu nu : YoungDiagram) :
    sE mu * sE nu = ∑ lam : DegreeShape (mu.card + nu.card),
      ((lrTableaux lam.val mu nu).card : ℤ) • sE lam.val := by
  set d := nu.card
  have h := eq_of_transform d (fun ν : DegreeShape d => sE mu * sE ν.val)
    (fun ν => ∑ lam : DegreeShape (mu.card + d), ((lrTableaux lam.val mu ν.val).card : ℤ) • sE lam.val)
    (fun β => by
      simp only [← mul_smul_comm, ← Finset.mul_sum, ← hE_expand]
      rw [skew_pieri0]
      rw [sum_degreeShape_eq (by rw [β.property]) (fun lam =>
        ((ofContent lam mu (TableauDominance.shapeContent β.val)).card : ℤ) • sE lam)]
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro lam _
      rw [← Finset.sum_smul, skew_kostka_lr0]
      congr 1
      rw [Nat.cast_sum]
      rw [sum_degreeShape_eq β.property (fun ν => ((lrTableaux lam.val mu ν).card *
        (tableauxOfContent ν (TableauDominance.shapeContent β.val)).card : ℕ) : YoungDiagram → ℤ)]
      apply Finset.sum_congr rfl
      intro ν _
      rw [K_apply]
      push_cast
      ring)
  exact congrFun h ⟨nu, rfl⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- **E Theorem 4.1 (the even Littlewood–Richardson rule)**: for all partitions `λ, μ, ν`, the
coefficient `c^λ_{μν}` of `s_λ` in `s_μ s_ν` equals the number of Littlewood–Richardson
tableaux of shape `λ/μ` and content `ν`. -/
theorem thm_4_1 (lam mu nu : YoungDiagram) :
    evenLR lam mu nu = (lrTableaux lam mu nu).card := by
  unfold evenLR
  rw [sE_mul_sE, map_sum]
  simp_rw [map_zsmul, ← sBasisE_apply, Basis.repr_self, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases h : lam.card = mu.card + nu.card
  · rw [Fintype.sum_eq_single (α := DegreeShape (mu.card + nu.card)) ⟨lam, h⟩ ?_]
    · simp
    · intro x hx
      rw [if_neg (fun h' => hx (Subtype.ext h'))]
  · rw [lrTableaux_eq_empty h, Finset.card_empty, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    intro h'
    exact h (h' ▸ x.property)

/-- `c^λ_{μν} = c^λ_{νμ}` (`Λ₁` is commutative). -/
theorem evenLR_comm (lam mu nu : YoungDiagram) : evenLR lam mu nu = evenLR lam nu mu := by
  unfold evenLR; rw [mul_comm']

/-- A combinatorial consequence: `#LR(λ/μ, ν) = #LR(λ/ν, μ)`. -/
theorem card_lrTableaux_comm (lam mu nu : YoungDiagram) :
    (lrTableaux lam mu nu).card = (lrTableaux lam nu mu).card := by
  have := evenLR_comm lam mu nu
  rw [thm_4_1, thm_4_1] at this
  exact_mod_cast this

/-- `c^λ_{μν} = 0` unless `|λ| = |μ| + |ν|` (E §4.1). -/
theorem evenLR_eq_zero {lam mu nu : YoungDiagram} (h : lam.card ≠ mu.card + nu.card) :
    evenLR lam mu nu = 0 := by
  rw [thm_4_1, lrTableaux_eq_empty h, Finset.card_empty, Nat.cast_zero]

end

end OddMath.Frontier.OddLREven
