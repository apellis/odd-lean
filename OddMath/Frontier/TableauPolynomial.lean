import OddMath.Frontier.SignedKostkaInvertibility

/-!
# Literal full bounded-alphabet tableau polynomials

The RAW sum before the shape prefactor in Ellis arXiv:1111.3932v1 (3.4).
This is not named a normalized Schur function. All words and tilde signs
are inherited unchanged from TableauEvaluation.
-/
namespace OddMath.Frontier.TableauPolynomial

open TableauSign TableauContent TableauEvaluation
open OddMath.SkewPolynomial
open scoped BigOperators

variable {μ : YoungDiagram}

/-- Encode only the actual finite cells, retaining the genuine SSYT laws. -/
noncomputable def alphabetEncoding (n : ℕ)
    (T : {T : PositiveTableau μ // InAlphabet n T}) : μ.cells → Fin (n + 1) :=
  fun p => ⟨T.val.entry p.val.1 p.val.2, Nat.lt_succ_of_le (T.property p.val p.property)⟩

theorem alphabetEncoding_injective (n : ℕ) :
    Function.Injective (alphabetEncoding (μ := μ) n) := by
  intro S T h
  apply Subtype.ext
  apply ext_cells
  intro p hp
  exact congrArg Fin.val (congrFun h ⟨p, hp⟩)

theorem finite_inAlphabet (n : ℕ) (μ : YoungDiagram) :
    Set.Finite {T : PositiveTableau μ | InAlphabet n T} := by
  haveI : Finite {T : PositiveTableau μ // InAlphabet n T} :=
    Finite.of_injective (alphabetEncoding n) (alphabetEncoding_injective n)
  exact Set.finite_coe_iff.mp (show Finite {T : PositiveTableau μ // InAlphabet n T}
    from inferInstance)

noncomputable def tableauxInAlphabet (n : ℕ) (μ : YoungDiagram) :
    Finset (PositiveTableau μ) := (finite_inAlphabet n μ).toFinset

@[simp] theorem mem_tableauxInAlphabet (n : ℕ) (T : PositiveTableau μ) :
    T ∈ tableauxInAlphabet n μ ↔ InAlphabet n T := by
  classical
  simp [tableauxInAlphabet]

/-- Literal RAW row-word sum, with no external shape sign. -/
noncomputable def tableauPolynomial (n : ℕ) (μ : YoungDiagram) : SkewPolynomial n :=
  ∑ T ∈ (tableauxInAlphabet n μ).attach,
    rowPolynomial n T.val ((mem_tableauxInAlphabet n T.val).mp T.property)

/-- Alphabet bounds also bound the support of actual content. -/
theorem content_bounded (n : ℕ) (T : PositiveTableau μ) (hT : InAlphabet n T)
    (k : ℕ) (hk : k ∈ (content T).support) : k ≤ n := by
  classical
  rw [Finsupp.mem_support_iff, content_apply] at hk
  obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp hk
  obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
  exact he ▸ hT p hp

/-- Exponent equality is the actual content fiber: zero and omitted labels count too. -/
theorem exponents_eq_iff_content (n : ℕ) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (c : ℕ →₀ ℕ) (h0 : c 0 = 0)
    (hc : ∀ k ∈ c.support, k ≤ n) :
    exponents n T = (fun i : Fin n => c (i.val + 1)) ↔ content T = c := by
  constructor
  · intro he
    ext k
    by_cases hk0 : k = 0
    · subst k
      simp [h0]
    · by_cases hkn : k ≤ n
      · have hh := congrFun he (⟨k - 1, by omega⟩ : Fin n)
        simpa only [exponents, Nat.sub_add_cancel (by omega : 1 ≤ k)] using hh
      · have ht : k ∉ (content T).support := fun hk => hkn (content_bounded n T hT k hk)
        have hc' : k ∉ c.support := fun hk => hkn (hc k hk)
        simp only [Finsupp.not_mem_support_iff.mp ht, Finsupp.not_mem_support_iff.mp hc']
  · intro he
    funext i
    exact congrArg (fun d : ℕ →₀ ℕ => d (i.val + 1)) he

theorem filter_exponents (n : ℕ) (μ : YoungDiagram) (c : ℕ →₀ ℕ) (h0 : c 0 = 0)
    (hc : ∀ k ∈ c.support, k ≤ n) :
    (tableauxInAlphabet n μ).filter (fun T =>
      exponents n T = (fun i : Fin n => c (i.val + 1))) = tableauxOfContent μ c := by
  classical
  ext T
  simp only [Finset.mem_filter, mem_tableauxInAlphabet, mem_tableauxOfContent]
  constructor
  · rintro ⟨hT, he⟩
    exact (exponents_eq_iff_content n T hT c h0 hc).mp he
  · intro he
    have ht := inAlphabet_of_mem n c hc T ((mem_tableauxOfContent T c).mpr he)
    exact ⟨ht, (exponents_eq_iff_content n T ht c h0 hc).mpr he⟩

/-- A consequence of literal evaluation, not the definition of the polynomial. -/
theorem tableauPolynomial_eq_sum (n : ℕ) (μ : YoungDiagram) :
    tableauPolynomial n μ = ∑ T ∈ tableauxInAlphabet n μ,
      monomial (exponents n T)
        ((-1 : ℤ) ^ (LrLegA.totalNorthLt (boxes T) (boxes T) + tildeWeight n T)) := by
  classical
  simp only [tableauPolynomial, rowPolynomial_eq]
  exact Finset.sum_attach (tableauxInAlphabet n μ) (fun T =>
    (monomial (exponents n T)
      ((-1 : ℤ) ^ (LrLegA.totalNorthLt (boxes T) (boxes T) + tildeWeight n T)) :
        SkewPolynomial n))

theorem coeff_tableauPolynomial (n : ℕ) (μ : YoungDiagram) (c : ℕ →₀ ℕ)
    (h0 : c 0 = 0) (hc : ∀ k ∈ c.support, k ≤ n) :
    tableauPolynomial n μ (fun i : Fin n => c (i.val + 1)) =
      ((-1 : ℤ) ^ (∑ i : Fin n, i.val * c (i.val + 1))) *
        ∑ T ∈ tableauxOfContent μ c,
          (-1 : ℤ) ^ LrLegA.totalNorthLt (boxes T) (boxes T) := by
  classical
  rw [tableauPolynomial_eq_sum]
  simp only [Finsupp.finset_sum_apply, monomial, Finsupp.single_apply]
  rw [← Finset.sum_filter, filter_exponents n μ c h0 hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have he := (mem_tableauxOfContent T c).mp hT
  simp only [tildeWeight, exponents, he, pow_add]
  ring

/-- The full polynomial and inherited fiber have exactly the same target coefficient. -/
theorem coeff_eq_contentPolynomial (n : ℕ) (μ : YoungDiagram) (c : ℕ →₀ ℕ)
    (h0 : c 0 = 0) (hc : ∀ k ∈ c.support, k ≤ n) :
    tableauPolynomial n μ (fun i : Fin n => c (i.val + 1)) =
      contentPolynomial n μ c hc (fun i : Fin n => c (i.val + 1)) := by
  rw [coeff_tableauPolynomial n μ c h0 hc, contentPolynomial_eq]
  simp only [monomial, Finsupp.single_eq_same]

/-- A zero relation in full polynomials induces a zero relation in each genuine
bounded content fiber. Off the target exponent, every fiber summand is zero. -/
theorem content_relation_of_full_relation {I : Type*} [Fintype I]
    (lam : I → YoungDiagram) (n : ℕ) (a : I → ℤ)
    (hz : ∑ i, a i • tableauPolynomial n (lam i) = 0)
    (c : ℕ →₀ ℕ) (h0 : c 0 = 0) (hc : ∀ k ∈ c.support, k ≤ n) :
    ∑ i, a i • contentPolynomial n (lam i) c hc = 0 := by
  classical
  ext e
  by_cases he : e = (fun i : Fin n => c (i.val + 1))
  · subst e
    have h := congrArg (fun f : SkewPolynomial n =>
      f (fun i : Fin n => c (i.val + 1))) hz
    simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.zero_apply] at h ⊢
    simpa only [coeff_eq_contentPolynomial n _ c h0 hc] using h
  · simp only [contentPolynomial_eq, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      monomial, Finsupp.single_apply, if_neg (Ne.symm he), smul_zero,
      Finset.sum_const_zero, Finsupp.zero_apply]

/-- Integral independence of the RAW full polynomials. The parent's actual
Kostka inverse and both unit signs are consumed through its proved fiber theorem. -/
theorem tableauPolynomial_independent {I : Type*} [Fintype I] [DecidableEq I]
    (lam : I → YoungDiagram) (hlam : Function.Injective lam) (n : ℕ)
    (hb : ∀ j p, p ∈ (lam j).cells → p.1 < n) (a : I → ℤ)
    (hz : ∑ i, a i • tableauPolynomial n (lam i) = 0) : ∀ i, a i = 0 := by
  apply SignedKostkaInvertibility.contentPolynomial_family_independent lam hlam n hb a
  intro j
  apply content_relation_of_full_relation lam n a hz
  rw [← TableauDominance.content_canonical]
  exact content_zero _

@[simp] theorem tableauxInAlphabet_empty (n : ℕ) :
    tableauxInAlphabet n ⊥ = {emptyTableau} := by
  classical
  ext T
  simp only [mem_tableauxInAlphabet, Finset.mem_singleton]
  constructor
  · intro _
    apply ext_cells
    simp
  · intro _ p hp
    simp at hp

@[simp] theorem tableauPolynomial_empty (n : ℕ) : tableauPolynomial n ⊥ = 1 := by
  classical
  rw [tableauPolynomial_eq_sum, tableauxInAlphabet_empty]
  have he : exponents n emptyTableau = 0 := by
    funext i
    simp [exponents]
  simp [he, tildeWeight, boxes, LrLegA.totalNorthLt]
  rfl

/-- Alphabet zero admits no positive filling of a nonempty genuine shape. -/
theorem tableauxInAlphabet_zero_of_ne_empty (μ : YoungDiagram) (hμ : μ ≠ ⊥) :
    tableauxInAlphabet 0 μ = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro T hT
  have h := (mem_tableauxInAlphabet 0 T).mp hT
  apply hμ
  apply YoungDiagram.ext
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  have hpos := T.positive ((YoungDiagram.mem_cells p).mp hp)
  have hle := h p hp
  omega

@[simp] theorem tableauPolynomial_zero_of_ne_empty (μ : YoungDiagram) (hμ : μ ≠ ⊥) :
    tableauPolynomial 0 μ = 0 := by
  rw [tableauPolynomial_eq_sum, tableauxInAlphabet_zero_of_ne_empty μ hμ]
  exact Finset.sum_empty

end OddMath.Frontier.TableauPolynomial
