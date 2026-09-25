import OddMath.Frontier.OddLRPlacticCor39

/-!
# Signed factorization counts of tableaux and odd Littlewood–Richardson coefficients

Ellis, *The odd Littlewood–Richardson rule*, arXiv:1111.3932v1 ("E"), §4.2, p. 14, proof of
Lemma 4.7, first line of (4.5):
  `c^λ_{μν} = (-1)^{dN(μ)+dN(ν)+dN(λ)+N(μ)+N(ν)+N(λ)}
      Σ_{U ∈ SSYT(μ), V ∈ SSYT(ν), UV = T_λ} sign(x̃^{w_r(U)} x̃^{w_r(V)}, x̃^{w_r(T_λ)})`.
E calls this "immediate from the definition of c^λ_{μν} and equation (3.4)"; it requires
Corollary 3.9 and the tableau basis of ℤPl_n.  This is the odd form of the factorization
count of Fulton, *Young Tableaux*, §5.1: the signed number of factorizations `U·V = T`
depends only on the shape of `T` (`pairCount_shape`).

Conventions: `N = n+2` letters; the product `U·V` of tableaux is `P(w_r(U) w_r(V))`, computed
by inserting `w_r(V)` into `U` (`prodState`); `pairSign U V` is the sign with
`w_r(U) w_r(V) = pairSign U V · w_r(U·V)` in ℤPl_N, equivalently
`x̃^{w_r(U)} x̃^{w_r(V)} = pairSign U V · x̃^{w_r(U·V)}` in OPol_N (`toSkew_pair`), i.e. E's
`sign(x̃^{w_r(U)} x̃^{w_r(V)}, x̃^{w_r(UV)})`.  `η(λ) = dN(λ) + N(λ)`.

Main results:
* `pairCount_shape` (odd Fulton factorization lemma): for tableaux T, T' of the same shape,
  `Σ_{UV=T} pairSign = Σ_{UV=T'} pairSign`.
* `shat_mul_shat`: `ŝ_μ ŝ_ν = Σ_λ c^λ_{μν} ŝ_λ` in ℤPl_N with `c^λ_{μν} = lrCoeff` given by
  (4.5), first line, evaluated at any tableau of shape λ (`lrCoeff_eq`), in particular at
  `T_λ` (`lrCoeff_canonical`); `sp_mul_sp` is its image in OPol_N.
* `lrCoeff_of_sK`: E Definition 4.6 — any expansion `s^K_μ s^K_ν = Σ c_λ s^K_λ` in OΛ has
  `c_λ = lrCoeff λ` for every λ with at most N rows.
-/

namespace OddMath.Frontier.OddLRPlactic

open scoped BigOperators
open TableauStripSigns TableauEvaluation TableauSign DegreeShapes

noncomputable section
set_option synthInstance.maxHeartbeats 200000
attribute [local instance] Classical.propDecidable

/-- `η(λ) = dN(λ) + N(λ)`, the exponent of the normalization (3.3)/(3.4). -/
abbrev eta (lam : YoungDiagram) : ℕ := directNorth lam + north lam

section Pairs
variable {N : ℕ} {mu nu : YoungDiagram}

/-- The product `U·V` of two tableaux in the plactic monoid: `U ← w_r(V)`. -/
def prodState (x : TabOf N mu × TabOf N nu) : State N :=
  (TableauWordInsertion.run N ⟨mu, x.1⟩ (rowFinWord N x.2.1 x.2.2)).1

/-- The sign of `w_r(U) w_r(V) = ± w_r(U·V)`. -/
def pairSign (x : TabOf N mu × TabOf N nu) : ℤ :=
  insSign ⟨mu, x.1⟩ (rowFinWord N x.2.1 x.2.2)

theorem word_pair (x : TabOf N mu × TabOf N nu) :
    OddPlactic.word N (rowFinWord N x.1.1 x.1.2) * OddPlactic.word N (rowFinWord N x.2.1 x.2.2) =
      pairSign x • tabWord N (prodState x) := by
  rw [← OddPlactic.word_append]
  exact word_rw_append ⟨mu, x.1⟩ _

/-- `pairSign U V = sign(x̃^{w_r(U)} x̃^{w_r(V)}, x̃^{w_r(UV)})` (E §4.2, p. 13). -/
theorem toSkew_pair (x : TabOf N mu × TabOf N nu) :
    PlacticEvaluation.toSkew N (OddPlactic.word N (rowFinWord N x.1.1 x.1.2)) *
      PlacticEvaluation.toSkew N (OddPlactic.word N (rowFinWord N x.2.1 x.2.2)) =
      pairSign x • PlacticEvaluation.toSkew N (tabWord N (prodState x)) := by
  rw [← map_mul, word_pair, map_zsmul]

theorem rowFinWord_length {lam : YoungDiagram} (T : PositiveTableau lam) (h : InAlphabet N T) :
    (rowFinWord N T h).length = lam.card := by
  rw [rowFinWord, List.length_map, List.length_attach, TableauRowWord.rowWord_length]

theorem prodState_card (x : TabOf N mu × TabOf N nu) :
    (prodState x).1.card = mu.card + nu.card := by
  have hs := TableauWordInsertion.run_spec N ⟨mu, x.1⟩ (rowFinWord N x.2.1 x.2.2)
  have hc := OddLRVerticalPieri.run_card N ⟨mu, x.1⟩ (rowFinWord N x.2.1 x.2.2)
  rw [Finset.card_sdiff hs.2.2.1, rowFinWord_length] at hc
  have hle := Finset.card_le_card hs.2.2.1
  change (prodState x).1.cells.card = mu.cells.card + nu.card
  change (prodState x).1.cells.card - mu.cells.card = nu.card at hc
  change mu.cells.card ≤ (prodState x).1.cells.card at hle
  omega

variable (mu nu) in
/-- The signed number of factorizations `U·V = T`, `U ∈ SSYT(μ)`, `V ∈ SSYT(ν)`. -/
def pairCount (S : State N) : ℤ :=
  ∑ x ∈ Finset.univ.filter (fun x : TabOf N mu × TabOf N nu => prodState x = S), pairSign x

end Pairs

/-! ## Coordinates in the tableau basis -/

theorem repr_tabWord {N : ℕ} (S : State N) :
    (tableauBasis N).repr (tabWord N S) = Finsupp.single S 1 := by
  rw [← tableauBasis_apply, Basis.repr_self]

theorem sum_single_apply {N : ℕ} (lam : YoungDiagram) (S : State N) :
    (∑ T : TabOf N lam, (Finsupp.single (⟨lam, T⟩ : State N) (1 : ℤ))) S =
      if S.1 = lam then 1 else 0 := by
  obtain ⟨sig, T0⟩ := S
  rw [Finsupp.finset_sum_apply]
  by_cases h : sig = lam
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single T0]
    · simp
    · intro T _ hT
      rw [Finsupp.single_apply, if_neg]
      intro he
      exact hT (eq_of_heq (Sigma.mk.inj_iff.mp he).2)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro T _
    rw [Finsupp.single_apply, if_neg]
    intro he
    exact h (Sigma.mk.inj_iff.mp he).1.symm

/-- The coordinates of ŝ_λ: `(-1)^{η(λ)}` on every tableau of shape λ. -/
theorem repr_shat {N : ℕ} (lam : YoungDiagram) (S : State N) :
    (tableauBasis N).repr (shat N lam) S = if S.1 = lam then (-1 : ℤ) ^ eta lam else 0 := by
  have h : shat N lam = (-1 : ℤ) ^ eta lam • ∑ T : TabOf N lam, tabWord N ⟨lam, T⟩ := rfl
  rw [h, map_zsmul, map_sum]
  simp only [repr_tabWord]
  rw [Finsupp.smul_apply, sum_single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem repr_shat_mul {N : ℕ} (mu nu : YoungDiagram) (S : State N) :
    (tableauBasis N).repr (shat N mu * shat N nu) S =
      (-1 : ℤ) ^ (eta mu + eta nu) * pairCount mu nu S := by
  have h : shat N mu * shat N nu = (-1 : ℤ) ^ (eta mu + eta nu) •
      ∑ x : TabOf N mu × TabOf N nu, pairSign x • tabWord N (prodState x) := by
    rw [shat, shat, smul_mul_smul_comm, ← pow_add, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    simp only [← word_pair]
  rw [h, map_zsmul, map_sum, Finsupp.smul_apply, smul_eq_mul, Finsupp.finset_sum_apply]
  congr 1
  rw [pairCount, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_zsmul, repr_tabWord, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

/-! ## The factorization lemma -/

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := by
  rw [← mul_pow]; norm_num

/-- Corollary 3.9 read in the tableau basis: there are coefficients `c` with
`(-1)^{η(μ)+η(ν)} Σ_{UV=T} pairSign = (-1)^{η(λ)} c_λ` for every tableau `T` of shape λ. -/
theorem exists_coeff (n : ℕ) (mu nu : YoungDiagram) :
    ∃ c : YoungDiagram → ℤ, ∀ S : State (n+2),
      (-1 : ℤ) ^ (eta mu + eta nu) * pairCount mu nu S = c S.1 * (-1 : ℤ) ^ eta S.1 := by
  have hm := shatSpan_mul_mem n (shat_mem_shatSpan (n+2) mu) (shat_mem_shatSpan (n+2) nu)
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hm
  refine ⟨c, fun S => ?_⟩
  rw [← repr_shat_mul, ← hc, map_finsuppSum, Finsupp.sum_apply]
  simp only [map_zsmul, Finsupp.smul_apply, repr_shat, smul_eq_mul, mul_ite, mul_zero]
  rw [Finsupp.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finsupp.not_mem_support_iff.mp h, zero_mul]

/-- **Odd factorization lemma** (Fulton, *Young Tableaux*, §5.1, in the form used by E
Lemma 4.7): for tableaux `T`, `T'` of the same shape, the signed numbers of factorizations
`U·V = T` and `U·V = T'` (U, V of shapes μ, ν) are equal. -/
theorem pairCount_shape (n : ℕ) (mu nu : YoungDiagram) {S S' : State (n+2)} (h : S.1 = S'.1) :
    pairCount mu nu S = pairCount mu nu S' := by
  obtain ⟨c, hc⟩ := exists_coeff n mu nu
  have e := (hc S).trans ((congrArg (fun l => c l * (-1 : ℤ) ^ eta l) h).trans (hc S').symm)
  have hu := neg_one_pow_mul_self (eta mu + eta nu)
  calc pairCount mu nu S = (-1 : ℤ) ^ (eta mu + eta nu) * ((-1 : ℤ) ^ (eta mu + eta nu) *
        pairCount mu nu S) := by rw [← mul_assoc, hu, one_mul]
    _ = _ := by rw [e, ← mul_assoc, hu, one_mul]

/-! ## Odd Littlewood–Richardson coefficients from (4.5) -/

/-- E (4.5), first line, at any tableau of shape λ with entries at most N (0 if none):
`(-1)^{η(μ)+η(ν)+η(λ)} Σ_{UV=T} sign(x̃^{w_r(U)} x̃^{w_r(V)}, x̃^{w_r(T)})`. -/
def lrCoeff (N : ℕ) (mu nu lam : YoungDiagram) : ℤ :=
  if h : ∃ S : State N, S.1 = lam then
    (-1 : ℤ) ^ (eta mu + eta nu + eta lam) * pairCount mu nu h.choose
  else 0

/-- (4.5) holds at every tableau of shape λ (not only at a chosen one). -/
theorem lrCoeff_eq (n : ℕ) (mu nu : YoungDiagram) (S : State (n+2)) :
    lrCoeff (n+2) mu nu S.1 = (-1 : ℤ) ^ (eta mu + eta nu + eta S.1) * pairCount mu nu S := by
  have h : ∃ S' : State (n+2), S'.1 = S.1 := ⟨S, rfl⟩
  rw [lrCoeff, dif_pos h, pairCount_shape n mu nu h.choose_spec]

theorem canonical_inAlphabet (N : ℕ) (lam : YoungDiagram) (hl : lam.colLen 0 ≤ N) :
    InAlphabet N (TableauDominance.canonicalTableau lam) := by
  intro p hp
  rw [TableauDominance.canonical_entry hp]
  have := YoungDiagram.mem_iff_lt_colLen.mp
    (lam.up_left_mem le_rfl (Nat.zero_le p.2) ((YoungDiagram.mem_cells _).mp hp))
  omega

/-- **E (4.5), first line**, at `T_λ`. -/
theorem lrCoeff_canonical (n : ℕ) (mu nu lam : YoungDiagram) (hl : lam.colLen 0 ≤ n+2) :
    lrCoeff (n+2) mu nu lam = (-1 : ℤ) ^ (eta mu + eta nu + eta lam) *
      pairCount mu nu (⟨lam, TableauDominance.canonicalTableau lam,
        canonical_inAlphabet (n+2) lam hl⟩ : State (n+2)) :=
  lrCoeff_eq n mu nu ⟨lam, _, canonical_inAlphabet (n+2) lam hl⟩

theorem pairCount_of_card (N : ℕ) (mu nu : YoungDiagram) (S : State N)
    (h : S.1.card ≠ mu.card + nu.card) : pairCount mu nu S = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  exfalso
  exact h ((Finset.mem_filter.mp hx).2 ▸ prodState_card x)

/-- `ŝ_μ ŝ_ν = Σ_{|λ|=|μ|+|ν|} c^λ_{μν} ŝ_λ` in ℤPl_{n+2}, with `c^λ_{μν} = lrCoeff` of (4.5). -/
theorem shat_mul_shat (n : ℕ) (mu nu : YoungDiagram) :
    letI := degreeFintype (mu.card + nu.card)
    shat (n+2) mu * shat (n+2) nu =
      ∑ lam : DegreeShape (mu.card + nu.card), lrCoeff (n+2) mu nu lam.val • shat (n+2) lam.val := by
  letI := degreeFintype (mu.card + nu.card)
  apply (Basis.ext_elem_iff (tableauBasis (n+2))).mpr
  intro S
  rw [repr_shat_mul, map_sum, Finsupp.finset_sum_apply]
  simp only [map_zsmul, Finsupp.smul_apply, repr_shat, smul_eq_mul, mul_ite, mul_zero]
  by_cases hd : S.1.card = mu.card + nu.card
  · rw [Fintype.sum_eq_single (show DegreeShape (mu.card + nu.card) from ⟨S.1, hd⟩)]
    · rw [if_pos rfl]
      dsimp only
      rw [lrCoeff_eq]
      have hu := neg_one_pow_mul_self (eta S.1)
      calc _ = (-1 : ℤ) ^ (eta mu + eta nu) * pairCount mu nu S *
            ((-1) ^ eta S.1 * (-1) ^ eta S.1) := by rw [hu, mul_one]
        _ = _ := by rw [pow_add]; ring
    · intro lam hne
      rw [if_neg]
      intro he
      exact hne (Subtype.ext he.symm)
  · rw [pairCount_of_card _ mu nu S hd, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro lam _
    rw [if_neg]
    intro he
    exact hd (he ▸ lam.property)

/-- The image in OPol_{n+2}: `s^p_μ s^p_ν = Σ_λ c^λ_{μν} s^p_λ` with `c` from (4.5). -/
theorem sp_mul_sp (n : ℕ) (mu nu : YoungDiagram) :
    letI := degreeFintype (mu.card + nu.card)
    CompleteTableauExpansion.sp (n+2) mu * CompleteTableauExpansion.sp (n+2) nu =
      ∑ lam : DegreeShape (mu.card + nu.card),
        lrCoeff (n+2) mu nu lam.val • CompleteTableauExpansion.sp (n+2) lam.val := by
  letI := degreeFintype (mu.card + nu.card)
  rw [← toSkew_shat, ← toSkew_shat, ← map_mul, shat_mul_shat, map_sum]
  simp only [map_zsmul, toSkew_shat]

/-- Coefficients of an s^p-expansion are unique on shapes with at most n+2 rows. -/
theorem coeff_unique (n d : ℕ) (a b : DegreeShape d → ℤ)
    (h : letI := degreeFintype d
      ∑ lam : DegreeShape d, a lam • CompleteTableauExpansion.sp (n+2) lam.val =
      ∑ lam : DegreeShape d, b lam • CompleteTableauExpansion.sp (n+2) lam.val)
    (lam : DegreeShape d) (hl : lam.val.colLen 0 ≤ n+2) : a lam = b lam := by
  letI := degreeFintype d
  set x : OddPlactic.Plactic (n+2) := ∑ mu : DegreeShape d, (a mu - b mu) • shat (n+2) mu.val
  have hx : x ∈ shatSpan (n+2) :=
    sum_mem fun mu _ => Submodule.smul_mem _ _ (shat_mem_shatSpan _ _)
  have h0 : PlacticEvaluation.toSkew (n+2) x = 0 := by
    simp only [x, sub_smul, Finset.sum_sub_distrib, map_sub, map_sum, map_zsmul, toSkew_shat, h,
      sub_self]
  have hx0 := toSkew_injOn (n+2) hx h0
  have hr := congrArg (fun y => (tableauBasis (n+2)).repr y
    (⟨lam.val, _, canonical_inAlphabet (n+2) lam.val hl⟩ : State (n+2))) hx0
  simp only [x, map_sum, map_zsmul, Finsupp.finset_sum_apply, Finsupp.smul_apply, repr_shat,
    smul_eq_mul, mul_ite, mul_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hr
  rw [Finset.sum_eq_single lam] at hr
  · rw [if_pos rfl] at hr
    have := (mul_eq_zero.mp hr).resolve_right (pow_ne_zero _ (by norm_num))
    omega
  · intro mu _ hne
    rw [if_neg]
    intro he
    exact hne (Subtype.ext he.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

open OddLREKIdentification (sK piN)

/-- **E Definition 4.6 and (4.5), first line**: if `s^K_μ s^K_ν = Σ_{|λ|=|μ|+|ν|} c_λ s^K_λ`
in OΛ, then `c_λ = lrCoeff (n+2) μ ν λ` for every λ with at most n+2 rows. -/
theorem lrCoeff_of_sK (n : ℕ) (mu nu : YoungDiagram)
    (c : DegreeShape (mu.card + nu.card) → ℤ)
    (hc : letI := degreeFintype (mu.card + nu.card)
      sK mu * sK nu = ∑ lam : DegreeShape (mu.card + nu.card), c lam • sK lam.val)
    (lam : DegreeShape (mu.card + nu.card)) (hl : lam.val.colLen 0 ≤ n+2) :
    c lam = lrCoeff (n+2) mu nu lam.val := by
  letI := degreeFintype (mu.card + nu.card)
  apply coeff_unique n _ c (fun lam => lrCoeff (n+2) mu nu lam.val) _ lam hl
  have h := congrArg (piN (n+2)) hc
  simp only [map_mul, map_sum, map_zsmul, OddLRThm38.sK_eq_sp] at h
  rw [← h, sp_mul_sp]

end

end OddMath.Frontier.OddLRPlactic
