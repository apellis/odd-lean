import OddMath.Frontier.CompleteTableauExpansion
import OddMath.Frontier.EKDualBases
import OddMath.Frontier.PbwRealization

/-!
# EK1107.5610v2 Theorem 3.7, identity (3.9): M′ = Kᵀ · diag((-1)^{C(λᵀ,2)}) · K

For every degree `d` and partitions `μ, ρ ⊢ d`:

    EKDualBases.Mh d μ ρ = Σ_{λ ⊢ d} (-1)^{Σ_j C(λᵀ_j,2)} K_{λμ} K_{λρ},

where `Mh` is the existing source `M′_{μρ} = (h_μ, h_ρ)` (EK (3.2); its all-ℕ-matrix
signed count is `EKDualBases.proposition_3_1_Mh`) and `K = TableauDominance.signedKostka`
(EK (3.7)). The printed exponent `λ₂+λ₄+⋯` is proved equal in parity
(`sign_eq_even_rows`), and `Σ_j C(λᵀ_j,2) = Σ_i i·λ_{i+1}` exactly.

Route (not the RSK bijection): extract the coefficient of the normal-ordered
monomial `x^ν` in the finite skew-polynomial model on both sides of the existing
Ellis 1111.3932 Theorem 3.8 (`CompleteTableauExpansion.complete_tableau_expansion`,
`h_{ρ₁}⋯h_{ρ_ℓ} = Σ_λ K_{λρ} s̃_λ`):
* left: the `x^ν` coefficient of an ordered product of complete polynomials is
  `tilde(ν)` times the signed ℕ-matrix count with margins `ρ` and `ν`
  (`prodH_apply`, by induction with the existing row-splitting convolution
  `EKPairingMatrices.pairing_convolution`);
* right: the `x^ν` coefficient of `s̃_λ` is `(-1)^{directNorth λ} tilde(ν) K_{λν}`
  (`sp_coeff`, from `TableauPolynomial.coeff_tableauPolynomial` and
  `CompleteTableauExpansion.canonical_sign`).
The entrywise RSK sign refinement (3.8) is NOT claimed here.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKKostkaValues
open OddMath.SkewPolynomial EKPairingMatrices

/-- Tilde normalisation of an exponent vector (letter `i` carries `(-1)^i`). -/
noncomputable def tilde {n : ℕ} (e : Fin n → ℕ) : ℤ := (-1 : ℤ) ^ (∑ i : Fin n, i.val * e i)

theorem tilde_add {n : ℕ} (a b : Fin n → ℕ) : tilde (a + b) = tilde a * tilde b := by
  unfold tilde
  rw [← pow_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Nat.mul_add]

theorem tilde_mul_self {n : ℕ} (a : Fin n → ℕ) : tilde a * tilde a = 1 := by
  unfold tilde
  rw [← mul_pow]; norm_num

/-- Coefficient convolution over coordinatewise splits. -/
noncomputable def conv {n : ℕ} (f g : SkewPolynomial n) (e : Fin n → ℕ) : ℤ :=
  ∑ u : Splits e, f (upper u) * g (lower u) * OddMath.skewSign (upper u) (lower u)

theorem conv_single_single {n : ℕ} (a b e : Fin n → ℕ) (r s : ℤ) :
    conv (Finsupp.single a r) (Finsupp.single b s) e =
      if a + b = e then r * s * OddMath.skewSign a b else 0 := by
  classical
  unfold conv
  by_cases h : a + b = e
  · rw [if_pos h]
    have hle : ∀ j, a j < e j + 1 := fun j => by
      have := congrFun h j
      simp only [Pi.add_apply] at this
      omega
    let u₀ : Splits e := fun j => ⟨a j, hle j⟩
    have hup : upper u₀ = a := rfl
    have hlo : lower u₀ = b := by
      funext j
      have := congrFun h j
      simp only [Pi.add_apply] at this
      show e j - a j = b j
      omega
    rw [Finset.sum_eq_single u₀]
    · rw [hup, hlo]; simp
    · intro u _ hu
      have hua : a ≠ upper u := by
        intro hua
        apply hu
        funext j
        apply Fin.ext
        exact (congrFun hua j).symm
      rw [Finsupp.single_apply, if_neg hua]
      simp
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro u _
    rw [Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h1 h2
    · exfalso
      apply h
      funext j
      have := (u j).isLt
      rw [h1, h2]
      simp only [Pi.add_apply, upper, lower]
      omega
    all_goals simp

theorem mul_apply_conv {n : ℕ} (f g : SkewPolynomial n) (e : Fin n → ℕ) :
    (f * g) e = conv f g e := by
  classical
  refine Finsupp.induction_linear f ?_ ?_ ?_
  · simp [conv]
  · intro f₁ f₂ h₁ h₂
    rw [_root_.add_mul, Finsupp.add_apply, h₁, h₂]
    simp only [conv, Finsupp.add_apply, _root_.add_mul, Finset.sum_add_distrib]
  · intro a r
    refine Finsupp.induction_linear g ?_ ?_ ?_
    · simp [conv]
    · intro g₁ g₂ h₁ h₂
      rw [_root_.mul_add, Finsupp.add_apply, h₁, h₂]
      simp only [conv, Finsupp.add_apply, _root_.mul_add, _root_.add_mul, Finset.sum_add_distrib]
    · intro b s
      rw [conv_single_single]
      change (OddMath.SkewPolynomial.mul (monomial a r) (monomial b s)) e = _
      rw [mul_monomial]
      simp only [monomial, Finsupp.single_apply]

/-! ## Complete polynomials: exact coefficients -/

open PbwRealization (exponents exponents_cons exponents_nil)

theorem sum_exponents {n : ℕ} (w : List (Fin n)) : ∑ i, exponents w i = w.length := by
  induction w with
  | nil => simp
  | cons j w ih =>
    rw [exponents_cons, List.length_cons]
    simp only [Pi.add_apply, Finset.sum_add_distrib, ih, expSingle, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    omega

theorem tilde_expSingle {n : ℕ} (j : Fin n) : tilde (expSingle j) = (-1 : ℤ) ^ j.val := by
  unfold tilde expSingle
  congr 1
  simp

theorem sorted_word_prod {n : ℕ} (w : List (Fin n)) (hw : w.Sorted (· ≤ ·)) :
    (w.map PlacticEvaluation.tildeGenerator).prod =
      monomial (exponents w) (tilde (exponents w)) := by
  induction w with
  | nil => simp [tilde]; rfl
  | cons j w ih =>
    obtain ⟨hj, hw'⟩ := List.sorted_cons.mp hw
    rw [List.map_cons, List.prod_cons, ih hw', exponents_cons]
    change ((-1 : ℤ) ^ j.val • monomial (expSingle j) 1) * monomial _ _ = _
    rw [smul_mul_assoc]
    change (-1 : ℤ) ^ j.val • OddMath.SkewPolynomial.mul (monomial (expSingle j) 1)
      (monomial (exponents w) (tilde (exponents w))) = _
    rw [mul_monomial, Finsupp.smul_single]
    congr 1
    have hs : OddMath.skewSign (expSingle j) (exponents w) = 1 := by
      unfold OddMath.skewSign OddMath.crossingCount
      rw [Finset.sum_eq_zero]
      · simp
      intro i _
      apply Finset.sum_eq_zero
      intro k hk
      have hki : k < i := (Finset.mem_filter.mp hk).2
      unfold expSingle
      split_ifs with hji
      · subst hji
        have : k ∉ w := fun hkw => absurd (hj k hkw) (not_le.mpr hki)
        simp [exponents, List.count_eq_zero_of_not_mem this]
      · simp
    rw [hs, tilde_add, tilde_expSingle]
    simp

theorem exponents_count {n : ℕ} (w : List (Fin n)) (a : Fin n) : exponents w a = w.count a := rfl

theorem monotone_unique {n k : ℕ} (f g : Fin k → Fin n) (hf : Monotone f) (hg : Monotone g)
    (h : exponents (List.ofFn f) = exponents (List.ofFn g)) : f = g := by
  have hp : List.Perm (List.ofFn f) (List.ofFn g) := List.perm_iff_count.mpr (fun a => congrFun h a)
  have he := List.eq_of_perm_of_sorted hp (List.sorted_le_ofFn_iff.mpr hf)
    (List.sorted_le_ofFn_iff.mpr hg)
  exact List.ofFn_injective he

theorem monotone_exists {n k : ℕ} (b : Fin n → ℕ) (hb : ∑ i, b i = k) :
    ∃ f : Fin k → Fin n, Monotone f ∧ exponents (List.ofFn f) = b := by
  classical
  let s : Multiset (Fin n) := ∑ i, Multiset.replicate (b i) i
  let L : List (Fin n) := Multiset.sort (· ≤ ·) s
  have hlen : L.length = k := by
    simp only [L, Multiset.length_sort, s, Multiset.card_sum, Multiset.card_replicate, hb]
  have hsorted : L.Sorted (· ≤ ·) := Multiset.sort_sorted _ _
  have hcount (a : Fin n) : L.count a = b a := by
    rw [← Multiset.coe_count, Multiset.sort_eq]
    show Multiset.count a (∑ i, Multiset.replicate (b i) i) = b a
    rw [Multiset.count_sum']
    simp only [Multiset.count_replicate, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  refine ⟨fun t => L.get (Fin.cast hlen.symm t), ?_, ?_⟩
  · intro s t hst
    exact hsorted.rel_get_of_le (show (Fin.cast hlen.symm s).val ≤ (Fin.cast hlen.symm t).val from hst)
  · have hL : List.ofFn (fun t => L.get (Fin.cast hlen.symm t)) = L := by
      apply List.ext_get
      · simp [hlen]
      · intro m h₁ h₂
        simp
    funext a
    rw [exponents_count, hL, hcount]

theorem completePoly_apply (n k : ℕ) (b : Fin n → ℕ) :
    FiniteCompleteElementary.completePoly n k b = if ∑ i, b i = k then tilde b else 0 := by
  classical
  unfold FiniteCompleteElementary.completePoly
  rw [Finsupp.finset_sum_apply]
  have hterm (f : Fin k → Fin n) :
      ((if Monotone f then (List.ofFn (fun i => PlacticEvaluation.tildeGenerator (f i))).prod
        else 0 : SkewPolynomial n) b) =
        if Monotone f ∧ exponents (List.ofFn f) = b then tilde b else 0 := by
    by_cases hf : Monotone f
    · have hm : (List.ofFn fun i => PlacticEvaluation.tildeGenerator (f i)) =
          (List.ofFn f).map PlacticEvaluation.tildeGenerator := by rw [List.map_ofFn]; rfl
      rw [if_pos hf, hm, sorted_word_prod _ (List.sorted_le_ofFn_iff.mpr hf)]
      simp only [monomial, Finsupp.single_apply]
      by_cases he : exponents (List.ofFn f) = b
      · rw [if_pos he, if_pos ⟨hf, he⟩, he]
      · rw [if_neg he, if_neg (fun h => he h.2)]
    · rw [if_neg hf, if_neg (fun h => hf h.1)]
      rfl
  simp only [hterm]
  split_ifs with hb
  · obtain ⟨f₀, hf₀, he₀⟩ := monotone_exists b hb
    rw [Finset.sum_eq_single f₀]
    · rw [if_pos ⟨hf₀, he₀⟩]
    · intro g _ hg
      rw [if_neg]
      rintro ⟨hgm, hge⟩
      exact hg (monotone_unique g f₀ hgm hf₀ (hge.trans he₀.symm))
    · simp
  · apply Finset.sum_eq_zero
    intro f _
    rw [if_neg]
    rintro ⟨_, he⟩
    apply hb
    rw [← he, sum_exponents, List.length_ofFn]


/-! ## Ordered complete products: coefficients are signed matrix counts -/

/-- Ordered product of complete polynomials, factor `i` of degree `β i`. -/
noncomputable def prodH (n : ℕ) {r : ℕ} (β : Fin r → ℕ) : SkewPolynomial n :=
  (List.ofFn (fun i => FiniteCompleteElementary.completePoly n (β i))).prod

theorem pairing_nil {n : ℕ} (β : Fin 0 → ℕ) (e : Fin n → ℕ) :
    pairing β e = if e = 0 then 1 else 0 := by
  by_cases he : e = 0
  · rw [if_pos he]
    have hβ : β = fun _ => 0 := funext (fun i => Fin.elim0 i)
    subst hβ; subst he
    exact pairing_zero_zero 0 n
  · rw [if_neg he]
    apply pairing_degree_mismatch
    intro h
    apply he
    funext j
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
    exact (Finset.sum_eq_zero_iff.mp h.symm) j (Finset.mem_univ j)

theorem pairing_one_row {n : ℕ} (k : ℕ) (α : Fin n → ℕ) :
    pairing (fun _ : Fin 1 => k) α = if ∑ j, α j = k then 1 else 0 := by
  by_cases h : ∑ j, α j = k
  · rw [if_pos h, ← h]
    exact pairing_single_row α
  · rw [if_neg h]
    apply pairing_degree_mismatch
    simpa [eq_comm] using h

theorem crossingCount_eq_crossCols {n : ℕ} (a b : Fin n → ℕ) :
    OddMath.crossingCount a b = crossCols a b := by
  unfold OddMath.crossingCount crossCols
  simp only [Finset.sum_filter]

theorem prodH_apply (n : ℕ) : ∀ {r : ℕ} (β : Fin r → ℕ) (e : Fin n → ℕ),
    prodH n β e = tilde e * pairing β e
  | 0, β, e => by
    rw [pairing_nil]
    change (Finsupp.single (0 : Fin n → ℕ) (1 : ℤ)) e = _
    rw [Finsupp.single_apply]
    by_cases he : e = 0
    · rw [if_pos he.symm, if_pos he, he]; simp [tilde]
    · rw [if_neg (Ne.symm he), if_neg he]; simp
  | r+1, β, e => by
    have hsplit : prodH n β = prodH n (fun i : Fin r => β i.castSucc) *
        FiniteCompleteElementary.completePoly n (β (Fin.last r)) := by
      unfold prodH
      rw [List.ofFn_succ', List.prod_concat]
    have hβ : β = Fin.addCases (fun i : Fin r => β i.castSucc) (fun _ : Fin 1 => β (Fin.last r)) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.addCases_left]; rfl
      · rw [Fin.addCases_right]
        congr 1
        apply Fin.ext
        simp [Subsingleton.elim j 0]
    rw [hsplit, mul_apply_conv]
    conv_rhs => rw [hβ, pairing_convolution, Finset.mul_sum]
    unfold conv
    apply Finset.sum_congr rfl
    intro u _
    rw [prodH_apply n (fun i : Fin r => β i.castSucc) (upper u), completePoly_apply,
      pairing_one_row]
    have hsum : upper u + lower u = e := by
      funext j
      have := (u j).isLt
      simp only [Pi.add_apply, upper, lower]
      omega
    have ht : tilde e = tilde (upper u) * tilde (lower u) := by rw [← tilde_add, hsum]
    rw [OddMath.skewSign, crossingCount_eq_crossCols, ht]
    split_ifs <;> ring


/-! ## Extraction of the `x^ν` coefficient on both sides of Theorem 3.8 -/

open DegreeShapes TableauDominance TableauStripSigns CompleteTableauExpansion
open TableauSign TableauContent TableauRowWord
attribute [local instance] DegreeShapes.degreeFintype

theorem H_eq_prodH (n : ℕ) (μ : YoungDiagram) :
    H n μ = prodH n (EKSemiorthogonality.rows μ) := by
  unfold H prodH YoungDiagram.rowLens EKSemiorthogonality.rows
  rw [List.ofFn_eq_map, ← List.map_coe_finRange, List.map_map, List.map_map]
  rfl

theorem Mh_eq_pairing (d : ℕ) (ν μ : DegreeShape d) :
    EKDualBases.Mh d ν μ = pairing (EKSemiorthogonality.rows ν.val) (EKSemiorthogonality.rows μ.val) := by
  rw [EKDualBases.proposition_3_1_Mh]
  rfl

theorem sp_coeff (lam ν : YoungDiagram) :
    (sp (ν.colLen 0) lam) (EKSemiorthogonality.rows ν) =
      (-1 : ℤ) ^ directNorth lam * tilde (EKSemiorthogonality.rows ν) * signedKostka lam ν := by
  have hrows : EKSemiorthogonality.rows ν =
      fun i : Fin (ν.colLen 0) => shapeContent ν (i.val + 1) := by
    funext i
    rw [SignedKostkaInvertibility.shapeContent_row]
    rfl
  have h0 : shapeContent ν 0 = 0 := by
    rw [← content_canonical]; exact content_zero _
  have hc := shapeContent_bounded (ν.colLen 0) ν (shape_row_bound ν)
  unfold sp
  rw [Finsupp.smul_apply, hrows, TableauPolynomial.coeff_tableauPolynomial _ _ _ h0 hc]
  unfold signedKostka tilde
  rw [canonical_sign]
  have he (T : PositiveTableau lam) :
      (-1 : ℤ) ^ LrLegA.totalNorthLt (boxes T) (boxes T) = tableauSign T := by
    rw [tableauSign, rowWord_inversions]
  simp only [he, smul_eq_mul, pow_add]
  ring

/-- EK1107.5610v2 Theorem 3.7, equation (3.9), with the existing `M′ = Mh`
and the existing signed Kostka numbers (3.7). The sign statistic is
`directNorth λ = Σ_j C(λᵀ_j, 2)` (see `directNorth_eq_choose`). -/
theorem Mh_eq_sum_kostka (d : ℕ) (μ ρ : DegreeShape d) :
    EKDualBases.Mh d μ ρ = ∑ lam : DegreeShape d,
      (-1 : ℤ) ^ directNorth lam.val * signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  have h1 := congrArg (fun p => p (EKSemiorthogonality.rows μ.val))
    (complete_tableau_expansion (μ.val.colLen 0) d ρ)
  simp only at h1
  rw [H_eq_prodH, prodH_apply, pairing_transpose, ← Mh_eq_pairing, Finsupp.finset_sum_apply] at h1
  simp only [Finsupp.smul_apply, sp_coeff, smul_eq_mul] at h1
  have ht := tilde_mul_self (EKSemiorthogonality.rows μ.val)
  have h2 := congrArg (fun z => tilde (EKSemiorthogonality.rows μ.val) * z) h1
  simp only at h2
  rw [← _root_.mul_assoc, ht, _root_.one_mul, Finset.mul_sum] at h2
  rw [h2]
  apply Finset.sum_congr rfl
  intro lam _
  linear_combination (signedKostka lam.val ρ.val * (-1 : ℤ) ^ directNorth lam.val *
    signedKostka lam.val μ.val) * ht


/-! ## The sign statistic: Σ_j C(λᵀ_j, 2), and its parity λ₂ + λ₄ + ⋯ -/

theorem directNorth_eq_sum_row (lam : YoungDiagram) :
    directNorth lam = ∑ p ∈ lam.cells, p.1 := by
  unfold directNorth
  apply Finset.sum_congr rfl
  intro p hp
  have he : lam.cells.filter (fun q => q.1 < p.1 ∧ q.2 = p.2) =
      (Finset.range p.1).map ⟨fun i => (i, p.2), fun a b h => by simpa using h⟩ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨q.1, h1, by rw [← h2]⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, hi, rfl⟩
      have hp' : (p.1, p.2) ∈ lam := by simpa using hp
      simpa using lam.up_left_mem (Nat.le_of_lt hi) le_rfl hp'
  rw [he, Finset.card_map, Finset.card_range]

theorem cells_box (lam : YoungDiagram) :
    (Finset.range (lam.colLen 0) ×ˢ Finset.range (lam.rowLen 0)).filter (fun p => p ∈ lam) =
      lam.cells := by
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, YoungDiagram.mem_cells]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · exact YoungDiagram.mem_iff_lt_colLen.mp (lam.up_left_mem le_rfl (Nat.zero_le _) h)
    · exact YoungDiagram.mem_iff_lt_rowLen.mp (lam.up_left_mem (Nat.zero_le _) le_rfl h)

/-- The source statistic Σ_j C(λᵀ_j, 2), columns j < λ₁. -/
theorem directNorth_eq_choose (lam : YoungDiagram) :
    directNorth lam = ∑ j ∈ Finset.range (lam.rowLen 0), (lam.colLen j).choose 2 := by
  classical
  rw [directNorth_eq_sum_row, ← cells_box, Finset.sum_filter, Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.choose_two_right, ← Finset.sum_range_id, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨lam.up_left_mem le_rfl (Nat.zero_le _) h, h⟩
  · intro _ _; rfl

/-- Row form: Σ_i i·λ_{i+1} (zero-based rows). -/
theorem directNorth_eq_rows (lam : YoungDiagram) :
    directNorth lam = ∑ i ∈ Finset.range (lam.colLen 0), i * lam.rowLen i := by
  classical
  rw [directNorth_eq_sum_row, ← cells_box, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter, Nat.mul_comm, ← Finset.card_range (lam.rowLen i), ← smul_eq_mul,
    ← Finset.sum_const]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter, Finset.mem_range, ← YoungDiagram.mem_iff_lt_rowLen]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨lam.up_left_mem (Nat.zero_le _) le_rfl h, h⟩
  · intro _ _; rfl

/-- Printed form of the sign: (-1)^(λ₂+λ₄+⋯), i.e. odd zero-based rows. -/
theorem sign_eq_even_rows (lam : YoungDiagram) :
    (-1 : ℤ) ^ directNorth lam =
      (-1 : ℤ) ^ (∑ i ∈ (Finset.range (lam.colLen 0)).filter (fun i => i % 2 = 1), lam.rowLen i) := by
  rw [directNorth_eq_rows, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
    Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  rw [pow_mul]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [if_neg (by omega), (Nat.even_iff.mpr h).neg_one_pow, one_pow]
  · rw [if_pos h, (Nat.odd_iff.mpr h).neg_one_pow]

/-- (3.9) with the printed sign (-1)^(λ₂+λ₄+⋯). -/
theorem Mh_eq_sum_kostka_printed (d : ℕ) (μ ρ : DegreeShape d) :
    EKDualBases.Mh d μ ρ = ∑ lam : DegreeShape d,
      (-1 : ℤ) ^ (∑ i ∈ (Finset.range (lam.val.colLen 0)).filter (fun i => i % 2 = 1),
        lam.val.rowLen i) * signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  rw [Mh_eq_sum_kostka]
  simp only [sign_eq_even_rows]

/-- (3.9) with the source binomial statistic Σ_j C(λᵀ_j, 2). -/
theorem Mh_eq_sum_kostka_choose (d : ℕ) (μ ρ : DegreeShape d) :
    EKDualBases.Mh d μ ρ = ∑ lam : DegreeShape d,
      (-1 : ℤ) ^ (∑ j ∈ Finset.range (lam.val.rowLen 0), (lam.val.colLen j).choose 2) *
        signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  rw [Mh_eq_sum_kostka]
  simp only [directNorth_eq_choose]

/-- Signed matrix count form (Prop 3.1 second formula composed with (3.9)). -/
theorem matrix_sum_eq_sum_kostka (d : ℕ) (μ ρ : DegreeShape d) :
    (∑ A : Mat (EKSemiorthogonality.rows μ.val) (EKSemiorthogonality.rows ρ.val),
      (-1 : ℤ) ^ crossing A) = ∑ lam : DegreeShape d,
      (-1 : ℤ) ^ directNorth lam.val * signedKostka lam.val μ.val * signedKostka lam.val ρ.val := by
  rw [← EKDualBases.proposition_3_1_Mh, Mh_eq_sum_kostka]

attribute [local instance] Classical.propDecidable

/-- Matrix form M′ = Kᵀ · diag((-1)^{n(λ)}) · K over the exhaustive degree-d index. -/
noncomputable def kostka (d : ℕ) : Matrix (DegreeShape d) (DegreeShape d) ℤ :=
  fun lam μ => signedKostka lam.val μ.val

theorem Mh_eq_matrix (d : ℕ) :
    EKDualBases.Mh d = (kostka d).transpose *
      Matrix.diagonal (fun lam : DegreeShape d => (-1 : ℤ) ^ directNorth lam.val) * kostka d := by
  ext μ ρ
  rw [Mh_eq_sum_kostka, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro lam _
  rw [Matrix.mul_diagonal]
  simp only [kostka, Matrix.transpose_apply]
  ring

end OddMath.Frontier.EKKostkaValues
