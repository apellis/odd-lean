import OddMath.Frontier.OddLRRule
import OddMath.Frontier.EKKostkaValues

/-!
# Lemma 4.7 of Ellis, arXiv:1111.3932v1

E Lemma 4.7, display (4.4), p.14:
`c^λ_{μν} = (-1)^{dN(μ)+dN(ν)+dN(λ)+N(μ)+Σ_i (λ/ν)_i |ν/i|} Σ_{U ∈ SSYT(μ), U T_ν = T_λ} (-1)^{N^<(U)}`,
the product `U T_ν` taken in the even plactic monoid (Knuth equivalence of row words). Here
`(λ/ν)_i = λ_i - ν_i` and `|ν/i| = ν_1 + ⋯ + ν_{i-1}` (E §3.2, p.9: `ν/i` removes rows `i` through
the bottom).

We derive (4.4) from Theorem 4.8 (`OddLRRule.thm_4_8`) and the RSK form of the
Littlewood–Richardson correspondence (`OddLRRule.sum_lr`), together with Fulton's fact
(E p.14, [Ful97, §5.2]): `U V = T_λ` in the plactic monoid forces `V = T_ν` (`eq_canonical_of_product`).
-/

namespace OddMath.Frontier.OddLRRule

open TableauSign TableauEvaluation TableauContent OddLRTableau EKClassicalPlactic DegreeShapes
open EKRskBijection (Pairs Tab rskRec)
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {lam mu : YoungDiagram} {r : ℕ}

/-! ## Building a skew tableau from its two blocks -/

theorem exists_of_blocks (U : Fin (mu.colLen 0) → Fin (lam.colLen 0) → ℕ)
    (hz0 : (rskRec (lam.colLen 0) (mu.colLen 0) U).1 = mu)
    (hz0e : ∀ p ∈ mu.cells, (rskRec (lam.colLen 0) (mu.colLen 0) U).2.2.1.entry p.1 p.2 = p.1 + 1)
    (V : Fin r → Fin (lam.colLen 0) → ℕ)
    (hP : nrows (rskRec (lam.colLen 0) (mu.colLen 0 + r) (EKPairingMatrices.join U V)).2.1.1 =
      nrows (TableauDominance.canonicalTableau lam)) :
    ∃ S : SkR lam mu r, matU S = U ∧ matV S = V := by
  have hj' := rskRec_join U r V
  have hsig := sigma_eq_of_nrows _ _ hP
  have hsh : (rskRec (lam.colLen 0) (mu.colLen 0 + r) (EKPairingMatrices.join U V)).1 = lam :=
    congrArg Sigma.fst hsig
  obtain ⟨h1, h2, h3⟩ := rskFrom_Q (lam.colLen 0) (mu.colLen 0)
    (rskRec (lam.colLen 0) (mu.colLen 0) U) r V
  rw [← hj'] at h1 h2 h3
  have hbd := (rskRec (lam.colLen 0) (mu.colLen 0 + r) (EKPairingMatrices.join U V)).2.2.2
  generalize hy : rskRec (lam.colLen 0) (mu.colLen 0 + r) (EKPairingMatrices.join U V) = y
    at hsig hsh h1 h2 h3 hbd
  obtain ⟨la, ⟨P', hP'⟩, ⟨Q', hQ'⟩⟩ := y
  dsimp only at hsig hsh h1 h2 h3 hbd
  subst hsh
  have hPeq : P' = TableauDominance.canonicalTableau la := by
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hsig
    exact hsig
  subst hPeq
  rw [hz0] at h1 h3
  have hfull : FullCond mu Q' := by
    refine ⟨YoungDiagram.cells_subset_iff.mp h1, fun i j h => ?_, fun i j h h' => ?_⟩
    · have hm : (i, j) ∈ (rskRec (la.colLen 0) (mu.colLen 0) U).1.cells := by
        rw [hz0]; simpa using h
      have := h2 (i, j) hm
      rw [hz0e (i, j) (by simpa using h)] at this
      exact this
    · exact h3 (i, j) (by simpa using h) (by simpa using h')
  let S' : SkR la mu r := ⟨fromFull Q' hfull, fun i j => by
    change (if (i, j) ∈ la ∧ (i, j) ∉ mu then Q'.entry i j - mu.colLen 0 else 0) ≤ r
    split_ifs with hc
    · have h' : Q'.entry i j ≤ mu.colLen 0 + r := hbd (i, j) (by simpa using hc.1)
      omega
    · omega⟩
  have hpair : pairOf S' = rskRec (la.colLen 0) (mu.colLen 0 + r) (EKPairingMatrices.join U V) := by
    rw [hy]
    unfold pairOf
    congr 3
    exact toFull_fromFull Q' hfull
  have hAeq : matA S' = EKPairingMatrices.join U V := (rskE _ _).injective (by
    change rskRec _ _ (matA S') = rskRec _ _ (EKPairingMatrices.join U V)
    rw [rsk_matA, hpair])
  refine ⟨S', ?_, ?_⟩
  · funext i
    change matA S' (Fin.castAdd r i) = _
    rw [hAeq]
    exact EKPairingMatrices.join_left _ _ _
  · funext i
    change matA S' (Fin.natAdd (mu.colLen 0) i) = _
    rw [hAeq]
    exact EKPairingMatrices.join_right _ _ _

/-! ## `U V = T_λ` forces `V = T_ν` -/

theorem yamR_append_right {u v : List ℕ} (h : YamR (u ++ v)) : YamR v :=
  ((yamR_append u v).mp h).1

/-- Fulton §5.2 (E p.14): if `U V = T_λ` in the plactic monoid then `V = T_ν`. -/
theorem eq_canonical_of_product {κ ν : YoungDiagram} (U : PositiveTableau κ)
    (V : PositiveTableau ν)
    (h : P (readR (nrows U) ++ readR (nrows V)) = nrows (TableauDominance.canonicalTableau lam)) :
    V = TableauDominance.canonicalTableau ν := by
  rw [← yamR_nrows_iff]
  apply yamR_append_right (u := readR (nrows U))
  rw [yamR_of_knuth (knuth_readR_P _), h, yamR_nrows_iff]

theorem knuth_of_P_eq {w w' : List ℕ} (h : P w = P w') : KnuthEquiv w w' :=
  knuth_trans (knuth_readR_P w) (by rw [h]; exact knuth_symm (knuth_readR_P w'))

/-! ## The objects of (4.4) -/

variable (lam mu) in
/-- `Σ_i (λ/ν)_i |ν/i|` (E (4.4)): `(λ_i - ν_i)(ν_1 + ⋯ + ν_{i-1})`, one-based rows. -/
def latticeCross (nu : YoungDiagram) : ℕ :=
  ∑ i ∈ Finset.range (lam.colLen 0), (lam.rowLen i - nu.rowLen i) * ∑ j ∈ Finset.range i, nu.rowLen j

variable (lam mu) in
/-- `{U ∈ SSYT(μ) : U T_ν = T_λ}`, the product in the even plactic monoid. -/
noncomputable def lemma47Set (nu : YoungDiagram) : Finset (PositiveTableau mu) :=
  (TableauPolynomial.tableauxInAlphabet (lam.colLen 0) mu).filter (fun U =>
    KnuthEquiv (TableauRowWord.rowWord U ++
      TableauRowWord.rowWord (TableauDominance.canonicalTableau nu))
      (TableauRowWord.rowWord (TableauDominance.canonicalTableau lam)))

theorem mem_lemma47Set {nu : YoungDiagram} {U : PositiveTableau mu} :
    U ∈ lemma47Set lam mu nu ↔ KnuthEquiv (TableauRowWord.rowWord U ++
      TableauRowWord.rowWord (TableauDominance.canonicalTableau nu))
      (TableauRowWord.rowWord (TableauDominance.canonicalTableau lam)) := by
  unfold lemma47Set
  rw [Finset.mem_filter, TableauPolynomial.mem_tableauxInAlphabet]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  intro p hp
  have hm : U.entry p.1 p.2 ∈ TableauRowWord.rowWord (TableauDominance.canonicalTableau lam) := by
    apply (perm_of_knuth h).subset
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨p, (TableauRowWord.mem_rowCells mu p).mpr hp, rfl⟩
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  have hq' := (TableauRowWord.mem_rowCells lam q).mp hq
  rw [← he, TableauDominance.canonical_entry hq']
  exact row_lt_colLen (show (q.1, q.2) ∈ lam from by simpa using hq')

/-! ## Counting -/

theorem length_filter_lt_succ (w : List ℕ) (n : ℕ) :
    (w.filter (fun y => decide (y < n + 1))).length =
      (w.filter (fun y => decide (y < n))).length + w.count n := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    by_cases h1 : z < n
    · rw [List.filter_cons_of_pos (by simp; omega), List.filter_cons_of_pos (by simpa using h1),
        List.count_cons_of_ne (by omega)]
      simp only [List.length_cons]; omega
    · by_cases h2 : z = n
      · subst h2
        rw [List.filter_cons_of_pos (by simp), List.filter_cons_of_neg (by simp),
          List.count_cons_self]
        simp only [List.length_cons]; omega
      · rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_neg (by simpa using h1),
          List.count_cons_of_ne (by omega)]
        exact ih

theorem length_filter_lt (w : List ℕ) : ∀ n,
    (w.filter (fun y => decide (y < n))).length = ∑ b ∈ Finset.range n, w.count b
  | 0 => by simp
  | n + 1 => by rw [length_filter_lt_succ, length_filter_lt w n, Finset.sum_range_succ]

theorem sum_map_count (g : ℕ → ℕ) (L : ℕ) : ∀ w : List ℕ, (∀ x ∈ w, 0 < x ∧ x ≤ L) →
    (w.map g).sum = ∑ i ∈ Finset.range L, w.count (i + 1) * g (i + 1)
  | [], _ => by simp
  | x :: w, h => by
    have hx := h x List.mem_cons_self
    rw [List.map_cons, List.sum_cons, sum_map_count g L w (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp only [List.count_cons, beq_iff_eq, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    obtain ⟨i, rfl⟩ : ∃ i, x = i + 1 := ⟨x - 1, by omega⟩
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg (fun h' => hb (by omega)), zero_mul]
    · intro hi; exact absurd (Finset.mem_range.mpr (by omega)) hi

theorem count_rowWord_canonical (κ : YoungDiagram) (i : ℕ) :
    (TableauRowWord.rowWord (TableauDominance.canonicalTableau κ)).count (i + 1) = κ.rowLen i := by
  rw [TableauRowWord.rowWord_count, TableauDominance.content_canonical, shapeContent_succ]

theorem count_rowWord_canonical_zero (κ : YoungDiagram) :
    (TableauRowWord.rowWord (TableauDominance.canonicalTableau κ)).count 0 = 0 := by
  rw [TableauRowWord.rowWord_count]; exact content_zero _

/-- The cross term of (4.9): sorting the letters of `U` past those of `T_ν`. -/
theorem crossL_lemma47 {nu : YoungDiagram} {U : PositiveTableau mu}
    (hU : U ∈ lemma47Set lam mu nu) (xs : List ℕ) (hxs : xs.Perm (TableauRowWord.rowWord U)) :
    EKRskSign.crossL xs (TableauRowWord.rowWord (TableauDominance.canonicalTableau nu)) =
      latticeCross lam nu := by
  have hk := mem_lemma47Set.mp hU
  have hp := perm_of_knuth hk
  unfold EKRskSign.crossL
  rw [(hxs.map _).sum_eq]
  have hb := (TableauPolynomial.mem_tableauxInAlphabet _ U).mp (Finset.mem_filter.mp hU).1
  rw [sum_map_count _ (lam.colLen 0)]
  · unfold latticeCross
    apply Finset.sum_congr rfl
    intro i _
    have hc := hp.count_eq (i + 1)
    rw [List.count_append, count_rowWord_canonical, count_rowWord_canonical] at hc
    rw [length_filter_lt, Finset.sum_range_succ', count_rowWord_canonical_zero, add_zero]
    simp_rw [count_rowWord_canonical]
    congr 1
    omega
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have hq' := (TableauRowWord.mem_rowCells mu q).mp hq
    exact ⟨U.positive (by simpa using hq'), hb q hq'⟩

/-! ## The correspondence `U ↔ (U-block, T_ν)` -/

theorem colLen_le_card (ν : YoungDiagram) : ν.colLen 0 ≤ ν.card := by
  have : (Finset.range (ν.colLen 0)).image (fun i => (i, 0)) ⊆ ν.cells := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    simpa using YoungDiagram.mem_iff_lt_colLen.mpr (Finset.mem_range.mp hi)
  have := Finset.card_le_card this
  rwa [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range] at this

theorem inAlphabet_of_mem {nu : YoungDiagram} {U : PositiveTableau mu}
    (hU : U ∈ lemma47Set lam mu nu) : InAlphabet (lam.colLen 0) U :=
  (TableauPolynomial.mem_tableauxInAlphabet _ U).mp (Finset.mem_filter.mp hU).1

theorem canonical_inAlphabet_of_mem {nu : YoungDiagram} {U : PositiveTableau mu}
    (hU : U ∈ lemma47Set lam mu nu) :
    InAlphabet (lam.colLen 0) (TableauDominance.canonicalTableau nu) := by
  have h := mem_lemma47Set.mp hU
  intro p hp
  have hm : (TableauDominance.canonicalTableau nu).entry p.1 p.2 ∈
      TableauRowWord.rowWord (TableauDominance.canonicalTableau lam) := by
    apply (perm_of_knuth h).subset
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨p, (TableauRowWord.mem_rowCells nu p).mpr hp, rfl⟩
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  have hq' := (TableauRowWord.mem_rowCells lam q).mp hq
  rw [← he, TableauDominance.canonical_entry hq']
  exact row_lt_colLen (show (q.1, q.2) ∈ lam from by simpa using hq')

theorem canonical_inAlphabet_card (ν : YoungDiagram) :
    InAlphabet ν.card (TableauDominance.canonicalTableau ν) := by
  intro p hp
  have := canonical_inAlphabet ν p hp
  have := colLen_le_card ν
  omega

variable (lam mu) in
/-- The upper block of `U`: `RSK⁻¹(U, T_μ)`. -/
noncomputable def umatOf (U : PositiveTableau mu) (hU : InAlphabet (lam.colLen 0) U) :
    Fin (mu.colLen 0) → Fin (lam.colLen 0) → ℕ :=
  (rskE _ _).symm ⟨mu, ⟨U, hU⟩, ⟨TableauDominance.canonicalTableau mu, canonical_inAlphabet mu⟩⟩

theorem rsk_umatOf (U : PositiveTableau mu) (hU : InAlphabet (lam.colLen 0) U) :
    rskRec (lam.colLen 0) (mu.colLen 0) (umatOf lam mu U hU) =
      ⟨mu, ⟨U, hU⟩, ⟨TableauDominance.canonicalTableau mu, canonical_inAlphabet mu⟩⟩ :=
  (rskE _ _).apply_symm_apply _

theorem insW_readR (X : List (List ℕ)) (hX : Valid X) (w : List ℕ) :
    insW X w = P (readR X ++ w) := by
  rw [P_append, P_readR X hX]

theorem P_rowWord {κ : YoungDiagram} (T : PositiveTableau κ) :
    P (TableauRowWord.rowWord T) = nrows T := by
  rw [rowWord_eq_readR_nrows, P_readR _ (nrows_valid T)]

theorem shapeExp_eq_directNorth (κ : YoungDiagram) :
    EKRskSign.shapeExp κ = TableauStripSigns.directNorth κ :=
  (EKKostkaValues.directNorth_eq_sum_row κ).symm

theorem sum_keys_lemma47 (nu : YoungDiagram) :
    ∑ U ∈ lemma47Set lam mu nu,
      (-1 : ℤ) ^ (TableauStripSigns.directNorth mu + TableauStripSigns.directNorth nu +
        TableauStripSigns.directNorth lam + TableauStripSigns.north lam + latticeCross lam nu) *
        TableauDominance.tableauSign U =
      ∑ k ∈ (keys lam mu nu.card).filter (fun k => k.2.1 = nu),
        kappa lam mu k * TableauDominance.tableauSign (TableauDominance.canonicalTableau nu) := by
  apply Finset.sum_bij (fun U hU => (umatOf lam mu U (inAlphabet_of_mem hU),
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
  · intro U hU
    have hU' := inAlphabet_of_mem hU
    have hs := rsk_sign (umatOf lam mu U hU')
    rw [rsk_umatOf] at hs
    change _ = (-1 : ℤ) ^ EKRskSign.shapeExp mu * TableauDominance.tableauSign U *
      TableauDominance.tableauSign (TableauDominance.canonicalTableau mu) at hs
    have hperm : (colword (umatOf lam mu U hU')).Perm (TableauRowWord.rowWord U) := by
      have h1 : P (colword (umatOf lam mu U hU')) = nrows U := by
        rw [← nrows_rskP, rsk_umatOf]
      have := perm_of_knuth (knuth_readR_P (colword (umatOf lam mu U hU')))
      rwa [h1, ← rowWord_eq_readR_nrows] at this
    have hcross := crossL_lemma47 hU _ hperm
    unfold kappa
    dsimp only
    rw [← rowWord_eq_readR_nrows, hcross, shapeExp_eq_directNorth, shapeExp_eq_directNorth]
    rw [shapeExp_eq_directNorth] at hs
    have hcl := CompleteTableauExpansion.canonical_sign lam
    have hcm := CompleteTableauExpansion.canonical_sign mu
    have hcn := CompleteTableauExpansion.canonical_sign nu
    unfold TableauDominance.tableauSign at *
    simp only [← pow_add] at hs hcl hcm hcn ⊢
    rw [EKRskSign.neg_one_pow_eq_iff] at hs hcl hcm hcn ⊢
    omega

/-- **E Lemma 4.7 (4.4)**: `c^λ_{μν} = (-1)^{dN(μ)+dN(ν)+dN(λ)+N(μ)+Σ_i (λ/ν)_i |ν/i|}
Σ_{U ∈ SSYT(μ), U T_ν = T_λ} (-1)^{N^<(U)}`. -/
theorem lemma_4_7 (lam mu nu : YoungDiagram) :
    oddLR lam mu nu =
      (-1 : ℤ) ^ (TableauStripSigns.directNorth mu + TableauStripSigns.directNorth nu +
        TableauStripSigns.directNorth lam + TableauStripSigns.north mu + latticeCross lam nu) *
        ∑ U ∈ lemma47Set lam mu nu, TableauDominance.tableauSign U := by
  rw [thm_4_8, lrSignedCount, sum_lr (r := nu.card) nu le_rfl, ← sum_keys_lemma47,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  rw [← mul_assoc]
  congr 1
  simp only [← pow_add]
  rw [EKRskSign.neg_one_pow_eq_iff]
  omega

end OddMath.Frontier.OddLRRule
