import OddMath.Frontier.OddLRExamplesSmallRank
import OddMath.Frontier.OddLRRuleLemma47
import OddMath.Frontier.OddLRMiscRemark

/-!
# The proof of Lemma 4.7 of Ellis, arXiv:1111.3932v1: display (4.5) and the sorting sign

E §4.2, p.14, proof of Lemma 4.7. The proof reads the odd Littlewood–Richardson coefficient off
the odd plactic ring `ℤPl_N`:
```
c^λ_{μν} = (-1)^{η(μ)+η(ν)+η(λ)} Σ_{U ∈ SSYT(μ), V ∈ SSYT(ν), UV = T_λ} sign(x̃^{w_r(U)} x̃^{w_r(V)}, x̃^{w_r(T_λ)})
         = (-1)^{η(μ)+η(ν)+η(λ)} Σ_{U ∈ SSYT(μ), U T_ν = T_λ} sign(x̃^{w_r(U)} x̃^{w_r(T_ν)}, x̃^{w_r(T_λ)}),
```
`η = dN + N`, and then computes the sign in two steps: ascend-sorting each of the three
monomials costs `(-1)^{N^<(U) + N(ν) + N(λ)}`, and merging the two sorted monomials costs
`Σ_i (λ/ν)_i |ν/i|` transpositions.

Here, for any alphabet size `N ≥ ℓ(λ)` (and `N ≥ ℓ(ν)` for the second line):
* `eq_4_5_first`: the first line, with `sign(Y, Z)` the library's `OddLRTableau.signBetween`
  and `UV` the product `OddLRPlactic.prodState` of `ℤPl_N`;
* `eq_canonical_of_prodState`: Fulton's fact "`UV = T_λ` forces `V = T_ν`" for this product;
* `eq_4_5_second`: the second line;
* `pairSign_eq_inversions`, `pairSign_sort`: the sorting-sign computation
  `sign(x̃^{w_r(U)} x̃^{w_r(T_ν)}, x̃^{w_r(T_λ)}) = sign(U) (-1)^{N(ν)+N(λ)+Σ_i (λ/ν)_i |ν/i|}`;
* `lemma_4_7_plactic`: Lemma 4.7 (4.4) obtained along this route, with the same index set as
  `OddLRRule.lemma_4_7` (`mem_lemma47Set_iff`).
-/

namespace OddMath.Frontier.OddLRExamples

open scoped BigOperators
open OddLRPlactic TableauSign TableauEvaluation DegreeShapes OddLRTableau
open OddMath.SkewPolynomial (SkewPolynomial)
open OddLREKIdentification (sK)
open TableauRowWord (inversions)

noncomputable section

attribute [local instance] Classical.propDecidable degreeFintype

/-! ## `c^λ_{μν}` in the odd plactic ring -/

/-- The canonical tableau `T_λ` as a tableau with entries at most `N`. -/
def canonTab (N : ℕ) (lam : YoungDiagram) (hl : lam.colLen 0 ≤ N) : TabOf N lam :=
  ⟨TableauDominance.canonicalTableau lam, canonical_inAlphabet N lam hl⟩

/-- `T_λ` as a state of `ℤPl_N`. -/
def canonState (N : ℕ) (lam : YoungDiagram) (hl : lam.colLen 0 ≤ N) : State N :=
  ⟨lam, canonTab N lam hl⟩

/-- The expansion of `s_μ s_ν` in the odd Schur basis, over the partitions of `|μ| + |ν|`
(E Definition 4.6; no Littlewood–Richardson rule is used). -/
theorem sK_mul_sK_degree (mu nu : YoungDiagram) :
    letI := degreeFintype (mu.card + nu.card)
    sK mu * sK nu = ∑ lam : DegreeShape (mu.card + nu.card), oddLR lam.val mu nu • sK lam.val := by
  letI := degreeFintype (mu.card + nu.card)
  set x := sK mu * sK nu
  conv_lhs => rw [← OddGrassmannSchur.sBasis.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hsub : (OddGrassmannSchur.sBasis.repr x).support ⊆
      (Finset.univ : Finset (DegreeShape (mu.card + nu.card))).map
        ⟨Subtype.val, Subtype.val_injective⟩ := by
    intro lam hlam
    rw [Finsupp.mem_support_iff] at hlam
    by_cases hd : lam.card = mu.card + nu.card
    · refine Finset.mem_map.mpr ⟨⟨lam, hd⟩, ?_, rfl⟩
      exact Finset.mem_univ (α := DegreeShape (mu.card + nu.card)) _
    · exact absurd (OddLRMisc.oddLR_eq_zero_of_card lam mu nu hd) hlam
  rw [Finset.sum_subset hsub (fun lam _ h => by
    rw [Finsupp.not_mem_support_iff.mp h, zero_smul]), Finset.sum_map]
  apply Finset.sum_congr rfl
  intro lam _
  simp only [Function.Embedding.coeFn_mk, OddGrassmannSchur.sBasis_apply]
  rfl

/-- `c^λ_{μν}` is the coefficient `lrCoeff` of `ŝ_λ` in `ŝ_μ ŝ_ν ∈ ℤPl_N`, for `ℓ(λ) ≤ N`
(Corollary 3.9; no Littlewood–Richardson rule is used). -/
theorem oddLR_eq_lrCoeff (N : ℕ) (lam mu nu : YoungDiagram) (hl : lam.colLen 0 ≤ N) :
    oddLR lam mu nu = lrCoeff N mu nu lam := by
  by_cases hd : lam.card = mu.card + nu.card
  · exact lrCoeff_of_sK_all N mu nu (fun lam => oddLR lam.val mu nu)
      (sK_mul_sK_degree mu nu) ⟨lam, hd⟩ hl
  · rw [OddLRMisc.oddLR_eq_zero_of_card lam mu nu hd]
    show 0 = lrCoeff N mu nu (canonState N lam hl).1
    rw [lrCoeff_eq_all N mu nu (canonState N lam hl), pairCount_of_card N mu nu _ hd, mul_zero]

/-- `x̃^{w_r(T)}` for a tableau with entries at most `N`. -/
abbrev xt {N : ℕ} {lam : YoungDiagram} (T : TabOf N lam) : SkewPolynomial N :=
  PlacticEvaluation.toSkew N (OddPlactic.word N (rowFinWord N T.1 T.2))

theorem xt_ne_neg {N : ℕ} {lam : YoungDiagram} (T : TabOf N lam) : xt T ≠ -xt T := by
  intro h
  have h' := congrArg (fun f : SkewPolynomial N => f (fun i => (rowFinWord N T.1 T.2).count i)) h
  simp only [xt, wordPolynomial_eq, OddMath.SkewPolynomial.monomial, Finsupp.coe_neg,
    Pi.neg_apply, Finsupp.single_eq_same] at h'
  have hu : ((-1 : ℤ) ^ (inversions ((rowFinWord N T.1 T.2).map Fin.val) +
      ((rowFinWord N T.1 T.2).map Fin.val).sum)) ≠ 0 := pow_ne_zero _ (by norm_num)
  omega

theorem signBetween_smul {M : Type*} [AddCommGroup M] {Y : M} (hY : Y ≠ -Y) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) : signBetween (ε • Y) Y = ε := by
  unfold signBetween
  rcases hε with rfl | rfl
  · simp
  · rw [neg_smul, one_smul, if_neg (fun h => hY h.symm), if_pos rfl]

theorem pairSign_sq {N : ℕ} {mu nu : YoungDiagram} (x : TabOf N mu × TabOf N nu) :
    pairSign x = 1 ∨ pairSign x = -1 := by
  unfold pairSign insSign
  rcases neg_one_pow_eq_or ℤ (TableauStripSigns.crossings N ⟨mu, x.1⟩ (rowFinWord N x.2.1 x.2.2))
    with h | h <;> simp [h]

/-- `pairSign U V = sign(x̃^{w_r(U)} x̃^{w_r(V)}, x̃^{w_r(UV)})` (E §4.2, p.13). -/
theorem pairSign_eq_signBetween {N : ℕ} {mu nu : YoungDiagram} (x : TabOf N mu × TabOf N nu) :
    pairSign x = signBetween (xt x.1 * xt x.2) (xt (prodState x).2) := by
  have h := toSkew_pair x
  change xt x.1 * xt x.2 = pairSign x • xt (prodState x).2 at h
  rw [h, signBetween_smul (xt_ne_neg _) (pairSign_sq x)]

/-- **E (4.5), first line**: for `ℓ(λ) ≤ N`,
`c^λ_{μν} = (-1)^{η(μ)+η(ν)+η(λ)} Σ_{UV = T_λ} sign(x̃^{w_r(U)} x̃^{w_r(V)}, x̃^{w_r(T_λ)})`. -/
theorem eq_4_5_first (N : ℕ) (lam mu nu : YoungDiagram) (hl : lam.colLen 0 ≤ N) :
    oddLR lam mu nu = (-1 : ℤ) ^ (eta mu + eta nu + eta lam) *
      ∑ x ∈ Finset.univ.filter (fun x : TabOf N mu × TabOf N nu => prodState x = canonState N lam hl),
        signBetween (xt x.1 * xt x.2) (xt (canonTab N lam hl)) := by
  rw [oddLR_eq_lrCoeff N lam mu nu hl]
  refine (lrCoeff_eq_all N mu nu (canonState N lam hl)).trans ?_
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [pairSign_eq_signBetween, (Finset.mem_filter.mp hx).2]
  rfl

/-! ## `UV = T_λ` forces `V = T_ν` -/

theorem nrows_prodState {N : ℕ} {mu nu : YoungDiagram} (x : TabOf N mu × TabOf N nu) :
    OddLRRule.nrows (prodState x).2.1 =
      EKClassicalPlactic.P (TableauRowWord.rowWord x.1.1 ++ TableauRowWord.rowWord x.2.1) := by
  unfold prodState
  rw [OddLRRule.nrows_run]
  have hl : (rowFinWord N x.2.1 x.2.2).map EKClassicalPlactic.lab = TableauRowWord.rowWord x.2.1 :=
    rowFinWord_labels N x.2.1 x.2.2
  rw [hl, OddLRRule.insW_readR _ (OddLRRule.nrows_valid _), ← OddLRRule.rowWord_eq_readR_nrows]

theorem prodState_eq_iff {N : ℕ} {mu nu lam : YoungDiagram} (hl : lam.colLen 0 ≤ N)
    (x : TabOf N mu × TabOf N nu) :
    prodState x = canonState N lam hl ↔
      EKClassicalPlactic.KnuthEquiv (TableauRowWord.rowWord x.1.1 ++ TableauRowWord.rowWord x.2.1)
        (TableauRowWord.rowWord (TableauDominance.canonicalTableau lam)) := by
  constructor
  · intro h
    apply OddLRRule.knuth_of_P_eq
    rw [← nrows_prodState, h, OddLRRule.P_rowWord]
    rfl
  · intro h
    apply state_ext
    apply OddLRRule.sigma_eq_of_nrows
    rw [nrows_prodState, EKClassicalPlactic.P_eq_of_knuth h, OddLRRule.P_rowWord]
    rfl

/-- **Fulton §5.2 (E p.14) for the product of `ℤPl_N`**: if `U·V = T_λ` then `V = T_ν`. -/
theorem eq_canonical_of_prodState {N : ℕ} {mu nu lam : YoungDiagram} (hl : lam.colLen 0 ≤ N)
    (x : TabOf N mu × TabOf N nu) (h : prodState x = canonState N lam hl) :
    x.2.1 = TableauDominance.canonicalTableau nu := by
  apply OddLRRule.eq_canonical_of_product (lam := lam) x.1.1
  rw [← OddLRRule.rowWord_eq_readR_nrows, ← OddLRRule.rowWord_eq_readR_nrows,
    ← nrows_prodState, h]
  rfl

/-- **E (4.5), second line**: for `ℓ(λ), ℓ(ν) ≤ N`,
`c^λ_{μν} = (-1)^{η(μ)+η(ν)+η(λ)} Σ_{U T_ν = T_λ} sign(x̃^{w_r(U)} x̃^{w_r(T_ν)}, x̃^{w_r(T_λ)})`. -/
theorem eq_4_5_second (N : ℕ) (lam mu nu : YoungDiagram) (hl : lam.colLen 0 ≤ N)
    (hn : nu.colLen 0 ≤ N) :
    oddLR lam mu nu = (-1 : ℤ) ^ (eta mu + eta nu + eta lam) *
      ∑ U ∈ Finset.univ.filter (fun U : TabOf N mu =>
          prodState (U, canonTab N nu hn) = canonState N lam hl),
        signBetween (xt U * xt (canonTab N nu hn)) (xt (canonTab N lam hl)) := by
  rw [eq_4_5_first N lam mu nu hl]
  congr 1
  symm
  apply Finset.sum_nbij (fun U => (U, canonTab N nu hn))
  · intro U hU
    simpa using hU
  · intro U _ U' _ h
    exact congrArg Prod.fst h
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    refine ⟨x.1, ?_, ?_⟩
    · have h2 : x.2 = canonTab N nu hn := Subtype.ext (eq_canonical_of_prodState hl x hx')
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [← h2]
      exact hx'
    · exact Prod.ext rfl (Subtype.ext (eq_canonical_of_prodState hl x hx').symm)
  · intro U _
    rfl

/-! ## The sorting sign -/

/-- `sign(x̃^{w_r(U)} x̃^{w_r(V)}, x̃^{w_r(UV)}) = (-1)^{N^<(w_r(U) w_r(V)) + N^<(w_r(UV))}`: the
sign of ascend-sorting the product and the result. -/
theorem pairSign_eq_inversions {N : ℕ} {mu nu : YoungDiagram} (x : TabOf N mu × TabOf N nu) :
    pairSign x = (-1 : ℤ) ^ (inversions (TableauRowWord.rowWord x.1.1 ++ TableauRowWord.rowWord x.2.1) +
      inversions (TableauRowWord.rowWord (prodState x).2.1)) := by
  set u := rowFinWord N x.1.1 x.1.2
  set v := rowFinWord N x.2.1 x.2.2
  have h1 := word_rw_append (⟨mu, x.1⟩ : State N) v
  have h2 := word_eq_inversions (rw (⟨mu, x.1⟩ : State N) ++ v)
  have hP : OddLRPlactic.P (rw (⟨mu, x.1⟩ : State N) ++ v) = prodState x := by
    have e := run_append (empty N) (rw (⟨mu, x.1⟩ : State N)) v
    have h' := P_rw (⟨mu, x.1⟩ : State N)
    unfold OddLRPlactic.P at h' ⊢
    rw [e, h']
    rfl
  rw [hP] at h2
  change OddPlactic.word N (rw ⟨mu, x.1⟩ ++ v) = pairSign x • tabWord N (prodState x) at h1
  have hc := congrArg (fun y => (tableauBasis N).repr y (prodState x)) (h1.symm.trans h2)
  simp only [map_zsmul, Finsupp.smul_apply, repr_tabWord, Finsupp.single_eq_same, smul_eq_mul,
    mul_one] at hc
  rw [hc]
  congr 2
  · have e : ((rw (⟨mu, x.1⟩ : State N) ++ v).map Fin.val).map (· + 1) =
        TableauRowWord.rowWord x.1.1 ++ TableauRowWord.rowWord x.2.1 := by
      rw [List.map_map, List.map_append]
      exact congrArg₂ (· ++ ·) (rowFinWord_labels N x.1.1 x.1.2) (rowFinWord_labels N x.2.1 x.2.2)
    rw [← e, inversions_map_succ]
  · exact rowFinWord_inversions N _ _

theorem neg_one_pow_inv_canonical (nu : YoungDiagram) :
    (-1 : ℤ) ^ inversions (TableauRowWord.rowWord (TableauDominance.canonicalTableau nu)) =
      (-1 : ℤ) ^ TableauStripSigns.north nu :=
  CompleteTableauExpansion.canonical_sign nu

/-- **The sorting sign of the proof of E Lemma 4.7** (steps 1 and 2, p.14): if `U T_ν = T_λ` then
`sign(x̃^{w_r(U)} x̃^{w_r(T_ν)}, x̃^{w_r(T_λ)}) = (-1)^{N^<(U)+N(ν)+N(λ)} (-1)^{Σ_i (λ/ν)_i |ν/i|}`. -/
theorem pairSign_sort {N : ℕ} {mu nu lam : YoungDiagram} (hl : lam.colLen 0 ≤ N)
    (hn : nu.colLen 0 ≤ N) (U : TabOf N mu)
    (h : prodState (U, canonTab N nu hn) = canonState N lam hl) :
    pairSign (U, canonTab N nu hn) = TableauDominance.tableauSign U.1 *
      (-1 : ℤ) ^ (TableauStripSigns.north nu + TableauStripSigns.north lam +
        OddLRRule.latticeCross lam nu) := by
  have hk := (prodState_eq_iff hl _).mp h
  have hmem : U.1 ∈ OddLRRule.lemma47Set lam mu nu := OddLRRule.mem_lemma47Set.mpr hk
  have hc := OddLRRule.crossL_lemma47 hmem _ (List.Perm.refl _)
  rw [pairSign_eq_inversions, h]
  change (-1 : ℤ) ^ (inversions (TableauRowWord.rowWord U.1 ++
    TableauRowWord.rowWord (TableauDominance.canonicalTableau nu)) +
    inversions (TableauRowWord.rowWord (TableauDominance.canonicalTableau lam))) = _
  rw [EKRskSign.inversions_append, hc, TableauDominance.tableauSign]
  simp only [pow_add]
  rw [neg_one_pow_inv_canonical, neg_one_pow_inv_canonical]
  ring

/-! ## Lemma 4.7 along the proof of E -/

theorem mem_lemma47Set_iff {N : ℕ} {mu nu lam : YoungDiagram} (hl : lam.colLen 0 ≤ N)
    (hn : nu.colLen 0 ≤ N) (U : TabOf N mu) :
    U.1 ∈ OddLRRule.lemma47Set lam mu nu ↔ prodState (U, canonTab N nu hn) = canonState N lam hl := by
  rw [OddLRRule.mem_lemma47Set, prodState_eq_iff hl]
  rfl

theorem sum_filter_eq_lemma47Set (N : ℕ) (lam mu nu : YoungDiagram) (hl : lam.colLen 0 ≤ N)
    (hn : nu.colLen 0 ≤ N) (f : PositiveTableau mu → ℤ) :
    ∑ U ∈ Finset.univ.filter (fun U : TabOf N mu =>
        prodState (U, canonTab N nu hn) = canonState N lam hl), f U.1 =
      ∑ U ∈ OddLRRule.lemma47Set lam mu nu, f U := by
  apply Finset.sum_nbij (fun U => U.1)
  · intro U hU
    exact (mem_lemma47Set_iff hl hn U).mpr (Finset.mem_filter.mp hU).2
  · intro U _ U' _ h
    exact Subtype.ext h
  · intro U hU
    have hb := (TableauPolynomial.mem_tableauxInAlphabet _ U).mp (Finset.mem_filter.mp hU).1
    refine ⟨⟨U, fun p hp => le_trans (hb p hp) hl⟩, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact (mem_lemma47Set_iff hl hn _).mp hU
  · intro U _
    rfl

/-- **E Lemma 4.7 (4.4), by the argument of E's proof**: (4.5) in `ℤPl_N`
(`N = max(ℓ(λ), ℓ(ν))`), Fulton's `UV = T_λ ⇒ V = T_ν` and the sorting sign give
`c^λ_{μν} = (-1)^{dN(μ)+dN(ν)+dN(λ)+N(μ)+Σ_i (λ/ν)_i |ν/i|} Σ_{U ∈ SSYT(μ), U T_ν = T_λ} (-1)^{N^<(U)}`.
This is `OddLRRule.lemma_4_7`, proved here without Theorem 4.8. -/
theorem lemma_4_7_plactic (lam mu nu : YoungDiagram) :
    oddLR lam mu nu =
      (-1 : ℤ) ^ (TableauStripSigns.directNorth mu + TableauStripSigns.directNorth nu +
        TableauStripSigns.directNorth lam + TableauStripSigns.north mu +
          OddLRRule.latticeCross lam nu) *
        ∑ U ∈ OddLRRule.lemma47Set lam mu nu, TableauDominance.tableauSign U := by
  set N := max (lam.colLen 0) (nu.colLen 0)
  have hl : lam.colLen 0 ≤ N := le_max_left _ _
  have hn : nu.colLen 0 ≤ N := le_max_right _ _
  rw [eq_4_5_second N lam mu nu hl hn, ← sum_filter_eq_lemma47Set N lam mu nu hl hn,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hU' := (Finset.mem_filter.mp hU).2
  have hs := pairSign_eq_signBetween (U, canonTab N nu hn)
  rw [hU'] at hs
  change pairSign (U, canonTab N nu hn) =
    signBetween (xt U * xt (canonTab N nu hn)) (xt (canonTab N lam hl)) at hs
  rw [← hs, pairSign_sort hl hn U hU']
  simp only [eta, pow_add]
  have hsq : ∀ k : ℕ, (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := fun k => by rw [← mul_pow]; norm_num
  have e1 := hsq (TableauStripSigns.north nu)
  have e2 := hsq (TableauStripSigns.north lam)
  linear_combination (TableauDominance.tableauSign U.1 * (-1) ^ TableauStripSigns.directNorth mu *
    (-1) ^ TableauStripSigns.directNorth nu * (-1) ^ TableauStripSigns.directNorth lam *
    (-1) ^ TableauStripSigns.north mu * (-1) ^ OddLRRule.latticeCross lam nu) *
    ((-1) ^ TableauStripSigns.north lam * (-1) ^ TableauStripSigns.north lam * e1 + e2)

end

end OddMath.Frontier.OddLRExamples
