import OddMath.Frontier.OddLRPlacticFactor
import OddMath.Frontier.SmallRank

/-!
# Corollary 3.9 and the factorization lemma in every rank

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), Corollary 3.9, p. 11, and
the factorization lemma used for Lemma 4.7 (E (4.5), first line), for an alphabet of `N` letters
with `N` arbitrary. For `N = n + 2 ≥ 2` these are `OddLRPlactic.cor39`,
`OddLRPlactic.pairCount_shape`, `OddLRPlactic.lrCoeff_eq`, `OddLRPlactic.shat_mul_shat` and
`OddLRPlactic.lrCoeff_of_sK`. Here the ranks `N = 0, 1` are added, where `OΛ_0 = OPol_0 = ℤ` and
`OΛ_1 = OPol_1 = ℤ[x]` (`SmallRank.OLam`, `SmallRank.zeroEquiv`, `SmallRank.rankOneEquiv`).

For `N ≤ 1` every shape carries at most one tableau with entries at most `N`
(`tabOf_subsingleton`), so every basis vector `w_r(T)` of `ℤPl_N` is `± ŝ_{sh(T)}` and the span of
the `ŝ_λ` is all of `ℤPl_N` (`shatSpan_eq_top`); the evaluation `ℤPl_N → OPol_N` is bijective.

* `cor39_all N : shatRing N ≃+* SmallRank.OLam N`, every `N`, with `cor39_all_apply`
  (`w ↦ x̃^w`) and `cor39_all_shat` (`ŝ_λ ↦ s^p_λ`); `cor39_zero : shatRing 0 ≃+* ℤ`,
  `cor39_one : shatRing 1 ≃+* ℤ[X]`.
* `pairCount_shape_all`, `lrCoeff_eq_all`, `shat_mul_shat_all`, `lrCoeff_of_sK_all`: every `N`.
-/

namespace OddMath.Frontier.OddLRExamples

open scoped BigOperators
open OddLRPlactic TableauSign TableauEvaluation DegreeShapes
open OddMath.SkewPolynomial (SkewPolynomial)

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## At most one tableau of each shape in ranks `0` and `1` -/

theorem tabOf_subsingleton {N : ℕ} (hN : N ≤ 1) (lam : YoungDiagram) (T T' : TabOf N lam) :
    T = T' := by
  apply Subtype.ext
  apply TableauContent.ext_cells
  intro p hp
  have h1 := T.2 p hp
  have h2 := T'.2 p hp
  have h3 := T.1.positive (show (p.1, p.2) ∈ lam from by simpa using hp)
  have h4 := T'.1.positive (show (p.1, p.2) ∈ lam from by simpa using hp)
  omega

theorem state_unique {N : ℕ} (hN : N ≤ 1) {S S' : State N} (h : S.1 = S'.1) : S = S' := by
  obtain ⟨lam, T⟩ := S
  obtain ⟨lam', T'⟩ := S'
  dsimp only at h
  subst h
  rw [tabOf_subsingleton hN lam T T']

theorem tabWord_eq_shat {N : ℕ} (hN : N ≤ 1) (S : State N) :
    tabWord N S = (-1 : ℤ) ^ eta S.1 • shat N S.1 := by
  haveI : Subsingleton (TabOf N S.1) := ⟨tabOf_subsingleton hN S.1⟩
  have h : shat N S.1 = (-1 : ℤ) ^ eta S.1 • ∑ T : TabOf N S.1, tabWord N ⟨S.1, T⟩ := rfl
  rw [h, Fintype.sum_subsingleton _ S.2, smul_smul, ← mul_pow]
  norm_num

/-- For `N ≤ 1` the `ŝ_λ` span `ℤPl_N`. -/
theorem shatSpan_eq_top {N : ℕ} (hN : N ≤ 1) : shatSpan N = ⊤ := by
  rw [eq_top_iff, ← span_tabWord N]
  apply Submodule.span_le.mpr
  rintro _ ⟨S, rfl⟩
  rw [tabWord_eq_shat hN]
  exact Submodule.smul_mem _ _ (shat_mem_shatSpan N S.1)

/-! ## The factorization lemma in every rank -/

/-- **Odd factorization lemma, every rank**: for tableaux `T`, `T'` of the same shape with
entries at most `N`, the signed numbers of factorizations `U·V = T` and `U·V = T'` agree. -/
theorem pairCount_shape_all (N : ℕ) (mu nu : YoungDiagram) {S S' : State N} (h : S.1 = S'.1) :
    pairCount mu nu S = pairCount mu nu S' := by
  by_cases hN : N ≤ 1
  · rw [state_unique hN h]
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    exact pairCount_shape n mu nu h

/-- E (4.5), first line, at every tableau of shape λ, every rank. -/
theorem lrCoeff_eq_all (N : ℕ) (mu nu : YoungDiagram) (S : State N) :
    lrCoeff N mu nu S.1 = (-1 : ℤ) ^ (eta mu + eta nu + eta S.1) * pairCount mu nu S := by
  have h : ∃ S' : State N, S'.1 = S.1 := ⟨S, rfl⟩
  rw [lrCoeff, dif_pos h, pairCount_shape_all N mu nu h.choose_spec]

/-- `ŝ_μ ŝ_ν = Σ_{|λ|=|μ|+|ν|} c^λ_{μν} ŝ_λ` in `ℤPl_N`, every rank. -/
theorem shat_mul_shat_all (N : ℕ) (mu nu : YoungDiagram) :
    letI := degreeFintype (mu.card + nu.card)
    shat N mu * shat N nu =
      ∑ lam : DegreeShape (mu.card + nu.card), lrCoeff N mu nu lam.val • shat N lam.val := by
  letI := degreeFintype (mu.card + nu.card)
  apply (Basis.ext_elem_iff (tableauBasis N)).mpr
  intro S
  rw [repr_shat_mul, map_sum, Finsupp.finset_sum_apply]
  simp only [map_zsmul, Finsupp.smul_apply, repr_shat, smul_eq_mul, mul_ite, mul_zero]
  by_cases hd : S.1.card = mu.card + nu.card
  · rw [Fintype.sum_eq_single (show DegreeShape (mu.card + nu.card) from ⟨S.1, hd⟩)]
    · rw [if_pos rfl]
      dsimp only
      rw [lrCoeff_eq_all]
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

/-- Coefficients of an `s^p`-expansion in `OPol_N` are unique on shapes with at most `N` rows,
every rank. -/
theorem coeff_unique_all (N d : ℕ) (a b : DegreeShape d → ℤ)
    (h : letI := degreeFintype d
      ∑ lam : DegreeShape d, a lam • CompleteTableauExpansion.sp N lam.val =
      ∑ lam : DegreeShape d, b lam • CompleteTableauExpansion.sp N lam.val)
    (lam : DegreeShape d) (hl : lam.val.colLen 0 ≤ N) : a lam = b lam := by
  letI := degreeFintype d
  set x : OddPlactic.Plactic N := ∑ mu : DegreeShape d, (a mu - b mu) • shat N mu.val
  have hx : x ∈ shatSpan N :=
    sum_mem fun mu _ => Submodule.smul_mem _ _ (shat_mem_shatSpan _ _)
  have h0 : PlacticEvaluation.toSkew N x = 0 := by
    simp only [x, sub_smul, Finset.sum_sub_distrib, map_sub, map_sum, map_zsmul, toSkew_shat, h,
      sub_self]
  have hx0 := toSkew_injOn N hx h0
  have hr := congrArg (fun y => (tableauBasis N).repr y
    (⟨lam.val, _, canonical_inAlphabet N lam.val hl⟩ : State N)) hx0
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

/-- **E Definition 4.6 and (4.5), first line, every rank**: if `s^K_μ s^K_ν = Σ c_λ s^K_λ` in
OΛ, then `c_λ = lrCoeff N μ ν λ` for every λ with at most `N` rows. -/
theorem lrCoeff_of_sK_all (N : ℕ) (mu nu : YoungDiagram)
    (c : DegreeShape (mu.card + nu.card) → ℤ)
    (hc : letI := degreeFintype (mu.card + nu.card)
      sK mu * sK nu = ∑ lam : DegreeShape (mu.card + nu.card), c lam • sK lam.val)
    (lam : DegreeShape (mu.card + nu.card)) (hl : lam.val.colLen 0 ≤ N) :
    c lam = lrCoeff N mu nu lam.val := by
  letI := degreeFintype (mu.card + nu.card)
  apply coeff_unique_all N _ c (fun lam => lrCoeff N mu nu lam.val) _ lam hl
  have h := congrArg (piN N) hc
  simp only [map_mul, map_sum, map_zsmul, OddLRThm38.sK_eq_sp] at h
  rw [← h, ← toSkew_shat, ← toSkew_shat, ← map_mul, shat_mul_shat_all, map_sum]
  simp only [map_zsmul, toSkew_shat]

/-! ## Corollary 3.9 in every rank -/

/-- **E Corollary 3.9, first half, every rank**: the span of the `ŝ_λ` is closed under
multiplication. -/
theorem shatSpan_mul_mem_all (N : ℕ) {x y : OddPlactic.Plactic N} (hx : x ∈ shatSpan N)
    (hy : y ∈ shatSpan N) : x * y ∈ shatSpan N := by
  by_cases hN : N ≤ 1
  · rw [shatSpan_eq_top hN]; exact Submodule.mem_top
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    exact shatSpan_mul_mem n hx hy

/-- The subring of `ℤPl_N` spanned by the `ŝ_λ`. -/
def shatRing (N : ℕ) : Subring (OddPlactic.Plactic N) where
  carrier := shatSpan N
  mul_mem' hx hy := shatSpan_mul_mem_all N hx hy
  one_mem' := one_mem_shatSpan N
  add_mem' hx hy := add_mem hx hy
  zero_mem' := zero_mem _
  neg_mem' hx := neg_mem hx

theorem mem_shatRing {N : ℕ} {x : OddPlactic.Plactic N} : x ∈ shatRing N ↔ x ∈ shatSpan N :=
  Iff.rfl

theorem toSkew_mem_OLam (N : ℕ) {x : OddPlactic.Plactic N} (hx : x ∈ shatSpan N) :
    PlacticEvaluation.toSkew N x ∈ SmallRank.OLam N := by
  by_cases hN : N ≤ 1
  · rw [SmallRank.OLam_small hN]; exact Subring.mem_top _
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    rw [SmallRank.OLam_add_two]
    exact toSkew_mem_kernel n ((mem_shatSubring_iff n x).mpr hx)

theorem exists_of_mem_OLam (N : ℕ) {f : SkewPolynomial N} (hf : f ∈ SmallRank.OLam N) :
    ∃ x ∈ shatSpan N, PlacticEvaluation.toSkew N x = f := by
  by_cases hN : N ≤ 1
  · obtain ⟨x, hx⟩ := PlacticEvaluation.toSkew_surjective N f
    exact ⟨x, by rw [shatSpan_eq_top hN]; exact Submodule.mem_top, hx⟩
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    rw [SmallRank.OLam_add_two] at hf
    obtain ⟨⟨x, hx⟩, hxf⟩ := evalHom_surjective n ⟨f, hf⟩
    exact ⟨x, (mem_shatSubring_iff n x).mp hx, congrArg Subtype.val hxf⟩

/-- The evaluation `w ↦ x̃^w` on the `ŝ`-subring, with values in `OΛ_N`, every rank. -/
def evalAll (N : ℕ) : shatRing N →+* SmallRank.OLam N :=
  (PlacticEvaluation.toSkew N).restrict (shatRing N) (SmallRank.OLam N)
    (fun _ hx => toSkew_mem_OLam N hx)

theorem evalAll_bijective (N : ℕ) : Function.Bijective (evalAll N) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    exact toSkew_injOn N x.2 (congrArg Subtype.val hx)
  · rintro ⟨f, hf⟩
    obtain ⟨x, hx, hxf⟩ := exists_of_mem_OLam N hf
    exact ⟨⟨x, hx⟩, Subtype.ext hxf⟩

/-- **E Corollary 3.9, every rank `N ≥ 0`**: the span of the `ŝ_λ` in `ℤPl_N` is a subring,
carried isomorphically onto `OΛ_N ⊂ OPol_N` by `w ↦ x̃^w`. -/
def cor39_all (N : ℕ) : shatRing N ≃+* SmallRank.OLam N :=
  RingEquiv.ofBijective (evalAll N) (evalAll_bijective N)

@[simp] theorem cor39_all_apply (N : ℕ) (x : shatRing N) :
    (cor39_all N x : SkewPolynomial N) = PlacticEvaluation.toSkew N x := rfl

/-- Under Corollary 3.9, `ŝ_λ ↦ s^p_λ`, every rank. -/
theorem cor39_all_shat (N : ℕ) (lam : YoungDiagram) :
    (cor39_all N ⟨shat N lam, shat_mem_shatSpan N lam⟩ : SkewPolynomial N) =
      CompleteTableauExpansion.sp N lam :=
  toSkew_shat N lam

/-- For `N ≥ 2` the subring of `cor39_all` is the subring `OddLRPlactic.shatSubring` of
`OddLRPlactic.cor39`. -/
theorem shatRing_add_two (n : ℕ) : shatRing (n + 2) = shatSubring n := by
  ext x
  rw [mem_shatRing, mem_shatSubring_iff]

/-- Corollary 3.9 in rank `0`: `ℤPl_0 ⊇ span(ŝ_λ) ≅ OΛ_0 = ℤ`. -/
def cor39_zero : shatRing 0 ≃+* ℤ :=
  (cor39_all 0).trans (Subring.topEquiv.trans SmallRank.zeroEquiv)

/-- Corollary 3.9 in rank `1`: `ℤPl_1 ⊇ span(ŝ_λ) ≅ OΛ_1 = ℤ[x]`. -/
def cor39_one : shatRing 1 ≃+* Polynomial ℤ :=
  (cor39_all 1).trans (Subring.topEquiv.trans SmallRank.rankOneEquiv)

/-- In ranks `0` and `1` the subring is all of `ℤPl_N`. -/
theorem shatRing_small {N : ℕ} (hN : N ≤ 1) : shatRing N = ⊤ := by
  ext x
  simp only [mem_shatRing, Subring.mem_top, iff_true]
  rw [shatSpan_eq_top hN]; exact Submodule.mem_top

end

end OddMath.Frontier.OddLRExamples
