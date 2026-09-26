import OddMath.Frontier.EKGeneralQClassical
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# EK §2.1 at q = 1: comparison with symmetric polynomials and the Hall inner product

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.1, p.8: "If `q = 1`, the inner product
`(h_β, h_α) = |βS_α|` is the number of double cosets, and it coincides with the standard inner
product on the bialgebra of symmetric functions `k[h₁, h₂, …]` in infinitely many variables
`x₁, x₂, …`, with `hₙ` being the `n`-th complete symmetric function."

Over an arbitrary commutative ring `k` and for `N` variables, let
`φ : Λ' → k[x₁, …, x_N]`, `hₙ ↦ hsymm N n` (Mathlib's complete homogeneous symmetric polynomial).

* `coeff_phi_vWord`: the coefficient of `x^d` in `φ(h_β)` is the number of `ℕ`-matrices with row
  sums `β` and column sums `d`.
* `coeff_phi_expo`: for every partition `μ` with at most `N` parts and every `x ∈ Λ'`, the
  coefficient of `x^μ = x₁^{μ₁}⋯x_N^{μ_N}` in `φ(x)` is `(x, h_μ)` at `q = 1`.
* `phi_eq_sum_msymm`: for `x ∈ Λ'ₙ`, `φ(x) = Σ_{μ ⊢ n} (x, h_μ) m_μ` with `m_μ` Mathlib's
  `msymm`; `phi_dualOne`: the dual basis to `{h_λ}` for the form maps to `{m_λ}`.  Hence the
  form is the standard (Hall) inner product, for which `h` and `m` are dual bases.
* `phi_eOne`: `φ(eₙ) = esymm N n` for the `eₙ` of EK p.9 (`EKGeneralQClassical.eOne`).
* `phiBar : Λ₁ →ₐ k[x₁,…,x_N]` is induced (`φ` kills `I₁`), and `ek_q1_symmetric_iso`: in every
  degree `n ≤ N` it identifies `Λ₁ₙ` with the symmetric polynomials of degree `n` in `N`
  variables (injective on `Λ₁ₙ`; onto the homogeneous symmetric polynomials of degree `n`, using
  Mathlib's fundamental theorem `esymmAlgHom_surjective`).
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKPairingMatrices DegreeShapes MvPolynomial
open EKFreeCoproduct (W degree partWord partWord_degree)
attribute [local instance] Classical.propDecidable degreeFintype

variable {k : Type*} [CommRing k]

/-! ## The comparison map -/

variable (k) in
/-- `φ : Λ' → k[x₁,…,x_N]`, `hₙ ↦ hsymm N n`. -/
def phi (N : ℕ) : L k →ₐ[k] MvPolynomial (Fin N) k :=
  FreeAlgebra.lift k (fun i => hsymm (Fin N) k (i + 1))

@[simp] theorem phi_h (N n : ℕ) : phi k N (h k n) = hsymm (Fin N) k n := by
  cases n with
  | zero => simp
  | succ n => exact FreeAlgebra.lift_ι_apply _ n

/-! ## Coefficients of `hsymm` -/

theorem prod_X_eq_monomial {σ : Type*} [DecidableEq σ] (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ k)).prod = monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]

theorem coeff_hsymm (N a : ℕ) (d : Fin N →₀ ℕ) :
    coeff d (hsymm (Fin N) k a) = if (∑ j, d j) = a then 1 else 0 := by
  classical
  rw [hsymm, coeff_sum]
  simp only [prod_X_eq_monomial, coeff_monomial]
  have hcard : Multiset.card (Finsupp.toMultiset d) = ∑ j, d j := by
    rw [Finsupp.card_toMultiset, Finsupp.sum_fintype]
    · rfl
    · intro; rfl
  split_ifs with hs
  · let s0 : Sym (Fin N) a := ⟨Finsupp.toMultiset d, hcard.trans hs⟩
    rw [Finset.sum_eq_single s0]
    · rw [if_pos]; simp [s0]
    · intro s _ hne
      rw [if_neg]
      intro he
      apply hne
      apply Sym.ext
      change s.1 = Finsupp.toMultiset d
      rw [← he, Multiset.toFinsupp_toMultiset]
    · simp
  · apply Finset.sum_eq_zero
    intro s _
    rw [if_neg]
    intro he
    apply hs
    rw [← hcard, ← he, Multiset.toFinsupp_toMultiset]
    exact s.2

/-! ## Coefficients of `φ(h_β)`: margin matrices -/

theorem sum_antidiagonal_eq_splits {N : ℕ} (d : Fin N →₀ ℕ) (f : (Fin N → ℕ) → (Fin N → ℕ) → k) :
    ∑ x ∈ Finset.antidiagonal d, f x.1 x.2 = ∑ u : Splits (⇑d), f (upper u) (lower u) := by
  symm
  apply Finset.sum_bij (fun u _ => (Finsupp.equivFunOnFinite.symm (upper u),
    Finsupp.equivFunOnFinite.symm (lower u)))
  · intro u _
    rw [Finset.mem_antidiagonal]
    ext j
    simp [split_add u j]
  · intro u _ v _ h
    funext j
    apply Fin.ext
    have := congrArg (fun x => (x.1 : Fin N →₀ ℕ) j) h
    simpa using this
  · intro x hx
    rw [Finset.mem_antidiagonal] at hx
    refine ⟨fun j => ⟨x.1 j, by have := congrArg (fun y => y j) hx; simp at this; omega⟩,
      Finset.mem_univ _, ?_⟩
    ext j
    · simp
    · have := congrArg (fun y => y j) hx
      simp at this
      simp [lower]
      omega
  · intro u _
    simp

theorem vWord_snoc {r : ℕ} (β : Fin (r + 1) → ℕ) :
    vWord k β = vWord k (Fin.init β) * h k (β (Fin.last r)) := by
  have hβ : β = Fin.addCases (Fin.init β) (fun _ : Fin 1 => β (Fin.last r)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have : Fin.last r = Fin.natAdd r (0 : Fin 1) := rfl
      rw [this, Fin.addCases_right]
    · have : Fin.castSucc j = Fin.castAdd 1 j := rfl
      rw [this, Fin.addCases_left]; rfl
  conv_lhs => rw [hβ]
  rw [vWord_join, vWord_singleton]

theorem matForm_snoc (q : k) {r c : ℕ} (β : Fin (r + 1) → ℕ) (α : Fin c → ℕ) :
    matForm q β α = ∑ u : Splits α, q ^ crossCols (upper u) (lower u) *
      matForm q (Fin.init β) (upper u) * matForm q (fun _ : Fin 1 => β (Fin.last r)) (lower u) := by
  have hβ : β = Fin.addCases (Fin.init β) (fun _ : Fin 1 => β (Fin.last r)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have : Fin.last r = Fin.natAdd r (0 : Fin 1) := rfl
      rw [this, Fin.addCases_right]
    · have : Fin.castSucc j = Fin.castAdd 1 j := rfl
      rw [this, Fin.addCases_left]; rfl
  conv_lhs => rw [hβ]
  rw [matForm_convolution]

/-- The coefficient of `x^d` in `φ(h_β)` is the number of `ℕ`-matrices with row sums `β` and
column sums `d`. -/
theorem coeff_phi_vWord (N : ℕ) {r : ℕ} (β : Fin r → ℕ) (d : Fin N →₀ ℕ) :
    coeff d (phi k N (vWord k β)) = matForm (1 : k) β ⇑d := by
  induction r generalizing d with
  | zero =>
    rw [vWord_nil, map_one, coeff_one]
    have h0 := matForm_single_row (1 : k) 0 ⇑d
    have e : matForm (1 : k) β ⇑d = matForm (1 : k) (fun _ : Fin 1 => 0) ⇑d := by
      rw [matForm_erase_zero_row (1 : k) (fun _ : Fin 1 => 0) (⇑d) 0 rfl]
      congr 1; funext i; exact Fin.elim0 i
    rw [e, h0]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [if_neg (Ne.symm hd), if_neg]
      intro hs
      apply hd
      ext j
      have := (Finset.sum_eq_zero_iff.mp hs) j (Finset.mem_univ j)
      simpa using this
  | succ r ih =>
    rw [vWord_snoc, map_mul, phi_h, coeff_mul, matForm_snoc]
    have e1 : ∑ x ∈ Finset.antidiagonal d,
        coeff x.1 (phi k N (vWord k (Fin.init β))) * coeff x.2 (hsymm (Fin N) k (β (Fin.last r))) =
        ∑ x ∈ Finset.antidiagonal d, (fun a b =>
          coeff (Finsupp.equivFunOnFinite.symm a) (phi k N (vWord k (Fin.init β))) *
          coeff (Finsupp.equivFunOnFinite.symm b) (hsymm (Fin N) k (β (Fin.last r))))
            ⇑x.1 ⇑x.2 := by
      apply Finset.sum_congr rfl
      intro x _
      simp
    rw [e1, sum_antidiagonal_eq_splits d (fun a b =>
      coeff (Finsupp.equivFunOnFinite.symm a) (phi k N (vWord k (Fin.init β))) *
        coeff (Finsupp.equivFunOnFinite.symm b) (hsymm (Fin N) k (β (Fin.last r))))]
    apply Finset.sum_congr rfl
    intro u _
    rw [ih, coeff_hsymm, matForm_single_row, one_pow, one_mul]
    simp

/-! ## Trailing zero columns -/

theorem sum_castLE {c c' : ℕ} (hc : c' ≤ c) (f : Fin c → ℕ) (hf : ∀ j : Fin c, c' ≤ j.val → f j = 0) :
    (∑ j, f j) = ∑ j : Fin c', f (Fin.castLE hc j) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hc) (f := f)
    (fun a _ b _ h => Fin.castLE_injective hc h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  apply hf
  by_contra hlt
  push_neg at hlt
  exact hj (Finset.mem_image.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/-- Deleting trailing zero columns does not change the set of margin matrices. -/
def matTrailingEquiv {r c c' : ℕ} (hc : c' ≤ c) (β : Fin r → ℕ) (α : Fin c → ℕ)
    (α' : Fin c' → ℕ) (h1 : ∀ j : Fin c', α (Fin.castLE hc j) = α' j)
    (h2 : ∀ j : Fin c, c' ≤ j.val → α j = 0) : Mat β α ≃ Mat β α' where
  toFun M := ⟨fun i j => M i (Fin.castLE hc j), by
    have hz : ∀ i (j : Fin c), c' ≤ j.val → M i j = 0 := fun i j hj => by
      have := entry_le M i j; rw [h2 j hj] at this; omega
    constructor
    · funext i
      rw [← congrFun M.property.1 i]
      exact (sum_castLE hc _ (hz i)).symm
    · funext j
      rw [← h1 j, ← congrFun M.property.2 (Fin.castLE hc j)]
      rfl⟩
  invFun M := ⟨fun i j => if h : j.val < c' then M i ⟨j.val, h⟩ else 0, by
    constructor
    · funext i
      rw [← congrFun M.property.1 i]
      change (∑ j : Fin c, if h : j.val < c' then M i ⟨j.val, h⟩ else 0) = _
      rw [sum_castLE hc _ (fun j hj => dif_neg (by omega))]
      apply Finset.sum_congr rfl
      intro j _
      rw [dif_pos (show (Fin.castLE hc j).val < c' from j.isLt)]
      rfl
    · funext j
      change (∑ i, if h : j.val < c' then M i ⟨j.val, h⟩ else 0) = α j
      by_cases hj : j.val < c'
      · simp only [dif_pos hj]
        have := congrFun M.property.2 ⟨j.val, hj⟩
        rw [← h1] at this
        exact this
      · simp only [dif_neg hj, Finset.sum_const_zero]
        exact (h2 j (by omega)).symm⟩
  left_inv M := by
    apply Subtype.ext
    funext i j
    change (if h : j.val < c' then M i (Fin.castLE hc ⟨j.val, h⟩) else 0) = M i j
    split_ifs with h
    · rfl
    · have := entry_le M i j; rw [h2 j (by omega)] at this; omega
  right_inv M := by
    apply Subtype.ext
    funext i j
    change (if h : (Fin.castLE hc j).val < c' then M i ⟨(Fin.castLE hc j).val, h⟩ else 0) = M i j
    rw [dif_pos (show (Fin.castLE hc j).val < c' from j.isLt)]
    rfl

theorem matForm_one_card {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    matForm (1 : k) β α = Fintype.card (Mat β α) := by
  simp [matForm]

open EKSemiorthogonality (rows)

/-- The exponent vector of a partition `μ` with at most `N` parts: `x^μ = x₁^{μ₁}⋯x_N^{μ_N}`. -/
def expo (N : ℕ) (μ : YoungDiagram) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => μ.rowLen j.val)

theorem matForm_expo {r : ℕ} (N : ℕ) (β : Fin r → ℕ) (μ : YoungDiagram) (hN : μ.colLen 0 ≤ N) :
    matForm (1 : k) β ⇑(expo N μ) = matForm (1 : k) β (rows μ) := by
  rw [matForm_one_card, matForm_one_card]
  congr 1
  exact Fintype.card_congr (matTrailingEquiv hN β _ _ (fun j => rfl)
    (fun j hj => EKLemma311Cond.rowLen_eq_zero_of_colLen_le μ hj))

/-- The Hall pairing: the coefficient of `x^μ` in `φ(x)` is `(x, h_μ)` at `q = 1`. -/
theorem coeff_phi_expo (N : ℕ) (μ : YoungDiagram) (hN : μ.colLen 0 ≤ N) (x : L k) :
    coeff (expo N μ) (phi k N x) = form (1 : k) x (hWord k μ.rowLens) := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => rw [map_add, coeff_add, hx, hy, map_add, LinearMap.add_apply]
  | hb w r =>
    rw [map_smul, coeff_smul, map_smul, LinearMap.smul_apply, ← vWord_parts,
      coeff_phi_vWord, matForm_expo N _ μ hN, hWord_rows, form_vWord]

/-! ## Symmetry, sorting, and antitone exponents -/

variable (k) in
/-- `φ` as a map into the symmetric subalgebra. -/
def phiSym (N : ℕ) : L k →ₐ[k] symmetricSubalgebra (Fin N) k :=
  FreeAlgebra.lift k (fun i => ⟨hsymm (Fin N) k (i + 1), hsymm_isSymmetric (Fin N) k _⟩)

theorem phi_eq_phiSym (N : ℕ) : phi k N = (symmetricSubalgebra (Fin N) k).val.comp (phiSym k N) := by
  apply FreeAlgebra.hom_ext
  funext i
  simp [phi, phiSym]

theorem phi_isSymmetric (N : ℕ) (x : L k) : (phi k N x).IsSymmetric := by
  rw [phi_eq_phiSym]
  exact (phiSym k N x).2

theorem exists_antitone_perm {N : ℕ} (d : Fin N → ℕ) :
    ∃ σ : Equiv.Perm (Fin N), Antitone (d ∘ σ) := by
  refine ⟨Tuple.sort (OrderDual.toDual ∘ d), fun i j hij => ?_⟩
  have := Tuple.monotone_sort (OrderDual.toDual ∘ d) hij
  exact OrderDual.toDual_le_toDual.mp this

theorem coeff_perm_of_symmetric {N : ℕ} {p : MvPolynomial (Fin N) k} (hp : p.IsSymmetric)
    (d : Fin N →₀ ℕ) (σ : Equiv.Perm (Fin N)) :
    coeff d p = coeff (Finsupp.equivFunOnFinite.symm (d ∘ σ)) p := by
  have h := coeff_rename_mapDomain σ σ.injective p (Finsupp.equivFunOnFinite.symm (d ∘ σ))
  rw [hp σ] at h
  rw [← h]
  congr 1
  ext j
  have e : j = σ (σ.symm j) := (σ.apply_symm_apply j).symm
  rw [e, Finsupp.mapDomain_apply σ.injective]
  simp

/-- A symmetric polynomial is determined by its coefficients at antitone exponents. -/
theorem symmetric_ext {N : ℕ} {p p' : MvPolynomial (Fin N) k} (hp : p.IsSymmetric)
    (hp' : p'.IsSymmetric)
    (h : ∀ g : Fin N →₀ ℕ, Antitone ⇑g → coeff g p = coeff g p') : p = p' := by
  ext d
  obtain ⟨σ, hσ⟩ := exists_antitone_perm ⇑d
  rw [coeff_perm_of_symmetric hp d σ, coeff_perm_of_symmetric hp' d σ]
  apply h
  simpa using hσ

/-- Cells of the Young diagram with row lengths `g₀ ≥ g₁ ≥ ⋯ ≥ g_{N-1}`. -/
def ydCells {N : ℕ} (g : Fin N → ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N) ×ˢ (Finset.range (∑ j, g j + 1))).filter
    (fun p => ∃ h : p.1 < N, p.2 < g ⟨p.1, h⟩)

theorem mem_ydCells {N : ℕ} (g : Fin N → ℕ) (p : ℕ × ℕ) :
    p ∈ ydCells g ↔ ∃ h : p.1 < N, p.2 < g ⟨p.1, h⟩ := by
  unfold ydCells
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨h, hp⟩
    refine ⟨⟨h, ?_⟩, h, hp⟩
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (g j))
      (Finset.mem_univ (⟨p.1, h⟩ : Fin N))
    omega

/-- The Young diagram with row lengths `g₀ ≥ g₁ ≥ ⋯ ≥ g_{N-1}`. -/
def ydOf {N : ℕ} (g : Fin N → ℕ) (hg : Antitone g) : YoungDiagram where
  cells := ydCells g
  isLowerSet := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hle hmem
    simp only [Finset.mem_coe, mem_ydCells] at hmem ⊢
    obtain ⟨h, hb⟩ := hmem
    have h1 : a' ≤ a := hle.1
    have h2 : b' ≤ b := hle.2
    refine ⟨by omega, ?_⟩
    have := hg (show (⟨a', by omega⟩ : Fin N) ≤ ⟨a, h⟩ from h1)
    simp only at this ⊢
    omega

theorem mem_ydOf {N : ℕ} (g : Fin N → ℕ) (hg : Antitone g) (p : ℕ × ℕ) :
    p ∈ ydOf g hg ↔ ∃ h : p.1 < N, p.2 < g ⟨p.1, h⟩ :=
  mem_ydCells g p

theorem rowLen_ydOf {N : ℕ} (g : Fin N → ℕ) (hg : Antitone g) (i : Fin N) :
    (ydOf g hg).rowLen i.val = g i := by
  apply le_antisymm
  · by_contra hlt
    push_neg at hlt
    have := YoungDiagram.mem_iff_lt_rowLen.mpr hlt
    rw [mem_ydOf] at this
    obtain ⟨_, h⟩ := this
    exact lt_irrefl _ h
  · by_contra hlt
    push_neg at hlt
    have hm : (i.val, (ydOf g hg).rowLen i.val) ∈ ydOf g hg := by
      rw [mem_ydOf]; exact ⟨i.isLt, hlt⟩
    exact lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp hm)

theorem colLen_ydOf_le {N : ℕ} (g : Fin N → ℕ) (hg : Antitone g) :
    (ydOf g hg).colLen 0 ≤ N := by
  by_contra hlt
  push_neg at hlt
  have := YoungDiagram.mem_iff_lt_colLen.mpr hlt
  rw [mem_ydOf] at this
  obtain ⟨h, _⟩ := this
  exact lt_irrefl _ h

theorem expo_ydOf {N : ℕ} (g : Fin N →₀ ℕ) (hg : Antitone ⇑g) : expo N (ydOf ⇑g hg) = g := by
  ext j
  simp [expo, rowLen_ydOf]

/-- For an antitone exponent `g`, the coefficient of `x^g` in `φ(x)` is `(x, h_{μ(g)})`. -/
theorem coeff_phi_antitone (N : ℕ) (g : Fin N →₀ ℕ) (hg : Antitone ⇑g) (x : L k) :
    coeff g (phi k N x) = form (1 : k) x (hWord k (ydOf ⇑g hg).rowLens) := by
  conv_lhs => rw [← expo_ydOf g hg]
  exact coeff_phi_expo N _ (colLen_ydOf_le _ hg) x

theorem rows_ydOf_sum {N : ℕ} (g : Fin N → ℕ) (hg : Antitone g) :
    (∑ i, rows (ydOf g hg) i) = ∑ j, g j := by
  have hle := colLen_ydOf_le g hg
  rw [sum_castLE hle g (fun j hj => by
    rw [← rowLen_ydOf g hg j]; exact EKLemma311Cond.rowLen_eq_zero_of_colLen_le _ hj)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← rowLen_ydOf g hg]
  rfl

theorem rows_ydOf_le_one {N : ℕ} (g : Fin N → ℕ) (hg : Antitone g) :
    (∀ i, rows (ydOf g hg) i ≤ 1) ↔ ∀ j, g j ≤ 1 := by
  have hle := colLen_ydOf_le g hg
  constructor
  · intro h j
    by_cases hj : j.val < (ydOf g hg).colLen 0
    · have := h ⟨j.val, hj⟩
      simpa [rows, rowLen_ydOf] using this
    · rw [← rowLen_ydOf g hg j, EKLemma311Cond.rowLen_eq_zero_of_colLen_le _ (by omega)]
      omega
  · intro h i
    have := h ⟨i.val, by have := i.isLt; omega⟩
    simpa [rows, ← rowLen_ydOf g hg] using this

/-! ## Elementary symmetric polynomials -/

theorem coeff_esymm (N m : ℕ) (d : Fin N →₀ ℕ) :
    coeff d (esymm (Fin N) k m) = if (∀ j, d j ≤ 1) ∧ (∑ j, d j) = m then 1 else 0 := by
  classical
  rw [esymm_eq_sum_monomial, coeff_sum]
  simp only [coeff_monomial]
  have hind : ∀ t : Finset (Fin N), (∑ i ∈ t, Finsupp.single i 1 : Fin N →₀ ℕ) = d ↔
      ∀ j, d j = if j ∈ t then 1 else 0 := by
    intro t
    constructor
    · rintro rfl j
      simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
    · intro h
      ext j
      simp [Finsupp.finset_sum_apply, Finsupp.single_apply, h j]
  by_cases hd : (∀ j, d j ≤ 1) ∧ (∑ j, d j) = m
  · rw [if_pos hd]
    let t0 := Finset.univ.filter (fun j => d j = 1)
    have ht0 : ∀ j, d j = if j ∈ t0 then 1 else 0 := by
      intro j
      have := hd.1 j
      by_cases h : d j = 1
      · simp [t0, h]
      · simp [t0, h]; omega
    have hcard : t0.card = m := by
      rw [← hd.2, Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      have := hd.1 j
      by_cases h : d j = 1
      · simp [h]
      · simp [h]; omega
    rw [Finset.sum_eq_single t0]
    · rw [if_pos ((hind t0).mpr ht0)]
    · intro t _ hne
      rw [if_neg]
      intro he
      apply hne
      ext j
      have h1 := (hind t).mp he j
      have h2 := ht0 j
      by_cases hj : j ∈ t <;> by_cases hj' : j ∈ t0 <;> simp_all
    · intro h
      exact absurd (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩) h
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro t ht
    rw [if_neg]
    intro he
    apply hd
    have h1 := (hind t).mp he
    refine ⟨fun j => by rw [h1 j]; split_ifs <;> omega, ?_⟩
    rw [← (Finset.mem_powersetCard.mp ht).2, Finset.card_eq_sum_ones]
    simp only [h1, Finset.sum_boole]
    simp

/-- `φ(eₘ) = esymm N m`. -/
theorem phi_eOne (N m : ℕ) : phi k N (eOne k m) = esymm (Fin N) k m := by
  apply symmetric_ext (phi_isSymmetric N _) (esymm_isSymmetric _ _ _)
  intro g hg
  rw [coeff_phi_antitone N g hg, hWord_rows, form_eOne_vWord, coeff_esymm,
    rows_ydOf_sum]
  exact if_congr (and_congr (rows_ydOf_le_one _ hg) Iff.rfl) rfl rfl

/-- Every symmetric polynomial in `N` variables is in the image of `φ` (Mathlib's fundamental
theorem of symmetric polynomials). -/
theorem symmetric_mem_range (N : ℕ) {p : MvPolynomial (Fin N) k}
    (hp : p ∈ symmetricSubalgebra (Fin N) k) : p ∈ (phi k N).range := by
  obtain ⟨P, hP⟩ := esymmAlgHom_surjective (σ := Fin N) (R := k) (n := N) (by simp) ⟨p, hp⟩
  have h1 : p = aeval (fun i : Fin N => esymm (Fin N) k (i + 1)) P := by
    rw [← esymmAlgHom_apply, hP]
  rw [h1]
  clear h1 hP
  induction P using MvPolynomial.induction_on with
  | C a => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    exact Subalgebra.mul_mem _ hp ⟨eOne k (i.val + 1), phi_eOne N _⟩

/-! ## Homogeneity -/

theorem hsymm_isHomogeneous (N a : ℕ) : (hsymm (Fin N) k a).IsHomogeneous a := by
  rw [hsymm]
  apply IsHomogeneous.sum
  intro s _
  rw [prod_X_eq_monomial]
  apply isHomogeneous_monomial
  have h := Multiset.toFinsupp_sum_eq s.1
  rw [Finsupp.sum] at h
  unfold Finsupp.degree
  exact h.trans s.2

theorem phi_word_isHomogeneous (N : ℕ) (w : W) :
    (phi k N (wordBasis k w)).IsHomogeneous (degree w) := by
  induction w using FreeMonoid.recOn with
  | h0 => rw [wordBasis_one, map_one]; exact isHomogeneous_one _ _
  | ih i w ih =>
    rw [wordBasis_mul, wordBasis_of, map_mul, phi_h, EKFreeCoproduct.degree_mul]
    exact (hsymm_isHomogeneous N (i + 1)).mul ih

/-- `φ` is graded: `φ(xₙ) = (φ x)ₙ`. -/
theorem phi_degreeProj (N n : ℕ) (x : L k) :
    phi k N (degreeProj k n x) = homogeneousComponent n (phi k N x) := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | hb w r =>
    rw [map_smul, map_smul, map_smul, map_smul, degreeProj_basis,
      homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr
        (phi_word_isHomogeneous N w))]
    by_cases hw : degree w = n
    · rw [if_pos hw, if_pos hw.symm]
    · rw [if_neg hw, if_neg (Ne.symm hw), map_zero]

theorem degreeProj_idem (n : ℕ) (x : L k) : degreeProj k n (degreeProj k n x) = degreeProj k n x := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => rw [map_add, map_add, hx, hy]
  | hb w r =>
    rw [map_smul, map_smul, degreeProj_basis]
    split_ifs with h
    · rw [degreeProj_basis, if_pos h]
    · rw [map_zero]

/-! ## Injectivity in degrees `n ≤ N` -/

theorem colLen_le_card (μ : YoungDiagram) : μ.colLen 0 ≤ μ.card := by
  rw [← YoungDiagram.length_rowLens, ← EKIntegralBases.rowLens_sum]
  exact List.length_le_sum_of_one_le _ (fun i hi => μ.pos_of_mem_rowLens i hi)

/-- In degree `n ≤ N`, `φ` detects the radical `I₁`. -/
theorem phi_injective_degree {n N : ℕ} (hn : n ≤ N) (x : L k) (hx : degreeProj k n x = x)
    (h0 : phi k N x = 0) : x ∈ radical (1 : k) := by
  intro y
  induction y using basis_induction k (wordBasis k) with
  | hz => simp
  | ha y z hy hz => rw [map_add, hy, hz, add_zero]
  | hb w r =>
    suffices hs : form (1 : k) x (wordBasis k w) = 0 by rw [map_smul, hs, smul_zero]
    by_cases hw : degree w = n
    · set β : Composition n := (wordEquiv n).symm ⟨w, hw⟩
      have hβ : partWord β.blocks = w :=
        congrArg Subtype.val ((wordEquiv n).apply_symm_apply ⟨w, hw⟩)
      have hb : wordBasis k w = hWord k β.blocks := by rw [← partWord_value, hβ]
      have hs := commutatorIdeal_le_radical (hWord_sort_sub_mem (k := k) β)
      have e : form (1 : k) x (hWord k β.blocks) =
          form (1 : k) x (hWord k (sortComp β).val.rowLens) := by
        rw [← sub_eq_zero, ← map_sub, form_symm]
        exact hs x
      rw [hb, e]
      have hc : (sortComp β).val.colLen 0 ≤ N := by
        have := colLen_le_card (sortComp β).val
        rw [(sortComp β).2] at this
        omega
      rw [← coeff_phi_expo N _ hc, h0, coeff_zero]
    · rw [← hx, form_degreeProj, degreeProj_basis, if_neg hw, map_zero]

/-! ## The induced map on `Λ₁` -/

variable (k) in
/-- `φ̄ : Λ₁ → k[x₁,…,x_N]`, induced by `φ` (the image is commutative, so `I₁` is killed). -/
def phiBar (N : ℕ) : Lam (1 : k) →ₐ[k] MvPolynomial (Fin N) k :=
  Ideal.Quotient.liftₐ (radical (1 : k)) (phi k N)
    (fun _ hx => lam_one_universal (phi k N).toRingHom (fun _ _ => mul_comm _ _) hx)

@[simp] theorem phiBar_pi (N : ℕ) (x : L k) : phiBar k N (piQ (1 : k) x) = phi k N x := rfl

@[simp] theorem phiBar_h (N n : ℕ) : phiBar k N (piQ (1 : k) (h k n)) = hsymm (Fin N) k n := by
  rw [phiBar_pi, phi_h]

/-- EK p.8, `q = 1`, in degree `n ≤ N`: `Λ₁ₙ` is identified with the symmetric polynomials of
degree `n` in `N` variables via `hₙ ↦ hsymm N n` (any commutative ring `k`). -/
theorem ek_q1_symmetric_iso {n N : ℕ} (hn : n ≤ N) :
    (∀ x : L k, degreeProj k n x = x → phiBar k N (piQ (1 : k) x) = 0 → piQ (1 : k) x = 0) ∧
    (∀ p : MvPolynomial (Fin N) k, p.IsSymmetric → p.IsHomogeneous n →
      ∃ x : L k, degreeProj k n x = x ∧ phiBar k N (piQ (1 : k) x) = p) ∧
    (∀ z : Lam (1 : k), (phiBar k N z).IsSymmetric) := by
  refine ⟨fun x hx h0 => (piQ_eq_zero_iff _ _).mpr (phi_injective_degree hn x hx h0), ?_, ?_⟩
  · intro p hp hph
    obtain ⟨y, hy⟩ := symmetric_mem_range N ((mem_symmetricSubalgebra p).mpr hp)
    refine ⟨degreeProj k n y, degreeProj_idem n y, ?_⟩
    have hy' : phi k N y = p := hy
    rw [phiBar_pi, phi_degreeProj, hy']
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hph), if_pos rfl]
  · intro z
    obtain ⟨x, rfl⟩ := piQ_surjective (1 : k) z
    exact phi_isSymmetric N x

/-! ## Monomial symmetric polynomials and the Hall inner product -/

/-- A partition of `n` (Young diagram) as Mathlib's `Nat.Partition n`. -/
def partOf {n : ℕ} (μ : DegreeShape n) : n.Partition where
  parts := ↑μ.val.rowLens
  parts_pos := fun hi => μ.val.pos_of_mem_rowLens _ (Multiset.mem_coe.mp hi)
  parts_sum := by rw [Multiset.sum_coe, EKIntegralBases.rowLens_sum, μ.2]

theorem coeff_msymm {N n : ℕ} (p : n.Partition) (d : Fin N →₀ ℕ) :
    coeff d (msymm (Fin N) k p) =
      if h : Multiset.card (Finsupp.toMultiset d) = n then
        (if Nat.Partition.ofSym (⟨Finsupp.toMultiset d, h⟩ : Sym (Fin N) n) = p then 1 else 0)
      else 0 := by
  classical
  rw [msymm, coeff_sum]
  simp only [prod_X_eq_monomial, coeff_monomial]
  split_ifs with h hp
  · let s0 : {a : Sym (Fin N) n // Nat.Partition.ofSym a = p} := ⟨⟨_, h⟩, hp⟩
    rw [Finset.sum_eq_single s0]
    · rw [if_pos]; simp [s0]
    · intro s _ hne
      rw [if_neg]
      intro he
      apply hne
      apply Subtype.ext
      apply Sym.ext
      change s.1.1 = Finsupp.toMultiset d
      rw [← he, Multiset.toFinsupp_toMultiset]
    · simp
  · apply Finset.sum_eq_zero
    intro s _
    rw [if_neg]
    intro he
    apply hp
    have : (⟨Finsupp.toMultiset d, h⟩ : Sym (Fin N) n) = s.1 := by
      apply Sym.ext
      change Finsupp.toMultiset d = s.1.1
      rw [← he, Multiset.toFinsupp_toMultiset]
    rw [this]
    exact s.2
  · apply Finset.sum_eq_zero
    intro s _
    rw [if_neg]
    intro he
    apply h
    rw [← he, Multiset.toFinsupp_toMultiset]
    exact s.1.2

theorem support_antitone {N : ℕ} (g : Fin N →₀ ℕ) (hg : Antitone ⇑g) :
    g.support = (Finset.univ : Finset (Fin ((ydOf ⇑g hg).colLen 0))).map
      (Fin.castLEEmb (colLen_ydOf_le _ hg)) := by
  ext j
  simp only [Finsupp.mem_support_iff, Finset.mem_map, Finset.mem_univ, true_and,
    Fin.castLEEmb_apply]
  rw [← rowLen_ydOf _ hg j]
  constructor
  · intro hne
    have hm : (j.val, 0) ∈ ydOf ⇑g hg := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
    exact ⟨⟨j.val, YoungDiagram.mem_iff_lt_colLen.mp hm⟩, Fin.ext rfl⟩
  · rintro ⟨i, rfl⟩
    have hm : (i.val, 0) ∈ ydOf ⇑g hg := YoungDiagram.mem_iff_lt_colLen.mpr i.isLt
    have := YoungDiagram.mem_iff_lt_rowLen.mp hm
    simp only [Fin.coe_castLE]
    omega

/-- The multiset of nonzero entries of an antitone exponent is the list of its row lengths. -/
theorem parts_ofSym_antitone {N n : ℕ} (g : Fin N →₀ ℕ) (hg : Antitone ⇑g)
    (h : Multiset.card (Finsupp.toMultiset g) = n) :
    (Nat.Partition.ofSym (⟨Finsupp.toMultiset g, h⟩ : Sym (Fin N) n)).parts =
      ↑(ydOf ⇑g hg).rowLens := by
  classical
  change (Finsupp.toMultiset g).dedup.map (fun j => (Finsupp.toMultiset g).count j) = _
  have hd : (Finsupp.toMultiset g).dedup = g.support.val := by
    rw [← Finsupp.toFinset_toMultiset]; rfl
  rw [hd]
  simp only [Finsupp.count_toMultiset]
  rw [support_antitone g hg, Finset.map_val, Multiset.map_map]
  rw [EKSemiorthogonality.rowLens_eq_ofFn, ← Fin.univ_val_map]
  congr 1
  funext i
  simp only [Function.comp_apply, Fin.castLEEmb_apply, rows]
  rw [← rowLen_ydOf _ hg (Fin.castLE _ i)]
  rfl

theorem ydOf_eq_iff {N n : ℕ} (g : Fin N →₀ ℕ) (hg : Antitone ⇑g)
    (h : Multiset.card (Finsupp.toMultiset g) = n) (μ : DegreeShape n) :
    Nat.Partition.ofSym (⟨Finsupp.toMultiset g, h⟩ : Sym (Fin N) n) = partOf μ ↔
      ydOf ⇑g hg = μ.val := by
  constructor
  · intro he
    have hp := congrArg Nat.Partition.parts he
    rw [parts_ofSym_antitone g hg h] at hp
    change (↑(ydOf ⇑g hg).rowLens : Multiset ℕ) = ↑μ.val.rowLens at hp
    have hl : (ydOf ⇑g hg).rowLens = μ.val.rowLens :=
      List.eq_of_perm_of_sorted (Multiset.coe_eq_coe.mp hp) (YoungDiagram.rowLens_sorted _)
        (YoungDiagram.rowLens_sorted _)
    apply YoungDiagram.equivListRowLens.injective
    exact Subtype.ext hl
  · intro he
    apply Nat.Partition.ext
    rw [parts_ofSym_antitone g hg h, he]
    rfl

theorem card_toMultiset_antitone {N : ℕ} (g : Fin N →₀ ℕ) (hg : Antitone ⇑g) :
    Multiset.card (Finsupp.toMultiset g) = (ydOf ⇑g hg).card := by
  rw [Finsupp.card_toMultiset, ← EKIntegralBases.rowLens_sum, EKSemiorthogonality.rowLens_eq_ofFn,
    List.sum_ofFn, rows_ydOf_sum, Finsupp.sum_fintype]
  · rfl
  · intro; rfl

/-- EK p.8, `q = 1`: under `φ`, the dual basis to `{h_λ}` for the form is the basis of monomial
symmetric polynomials; i.e. the form is the Hall inner product, `⟨h_λ, m_μ⟩ = δ_{λμ}`. -/
theorem phi_dualOne (N : ℕ) {n : ℕ} (μ : DegreeShape n) :
    phi k N (dualOne k μ.val) = msymm (Fin N) k (partOf μ) := by
  apply symmetric_ext (phi_isSymmetric N _) (msymm_isSymmetric _ _ _)
  intro g hg
  rw [coeff_phi_antitone N g hg, form_symm, form_dualOne, coeff_msymm]
  by_cases hν : ydOf ⇑g hg = μ.val
  · have hc : Multiset.card (Finsupp.toMultiset g) = n := by
      rw [card_toMultiset_antitone g hg, hν, μ.2]
    rw [if_pos hν, dif_pos hc, if_pos ((ydOf_eq_iff g hg hc μ).mpr hν)]
  · rw [if_neg hν]
    split_ifs with hc h2
    · exact absurd ((ydOf_eq_iff g hg hc μ).mp h2) hν
    · rfl
    · rfl

/-- EK p.8, `q = 1`: for `x ∈ Λ'ₙ`, `φ(x) = Σ_{μ ⊢ n} (x, h_μ) m_μ` (any `N`). -/
theorem phi_eq_sum_msymm (N n : ℕ) (x : L k) (hx : degreeProj k n x = x) :
    phi k N x = ∑ μ : DegreeShape n, form (1 : k) x (hWord k μ.val.rowLens) •
      msymm (Fin N) k (partOf μ) := by
  apply symmetric_ext (phi_isSymmetric N _)
  · exact (mem_symmetricSubalgebra _).mp (Subalgebra.sum_mem _ (fun μ _ =>
      Subalgebra.smul_mem _ ((mem_symmetricSubalgebra _).mpr (msymm_isSymmetric _ _ _)) _))
  intro g hg
  rw [coeff_phi_antitone N g hg, coeff_sum]
  simp only [coeff_smul, coeff_msymm, smul_eq_mul]
  by_cases hc : Multiset.card (Finsupp.toMultiset g) = n
  · have hν : (ydOf ⇑g hg).card = n := by rw [← card_toMultiset_antitone g hg, hc]
    rw [Finset.sum_eq_single ⟨ydOf ⇑g hg, hν⟩]
    · rw [dif_pos hc, if_pos ((ydOf_eq_iff g hg hc _).mpr rfl), mul_one]
    · intro μ _ hne
      rw [dif_pos hc, if_neg, mul_zero]
      intro he
      apply hne
      exact Subtype.ext ((ydOf_eq_iff g hg hc μ).mp he).symm
    · simp
  · rw [Finset.sum_eq_zero (fun μ _ => by rw [dif_neg hc, mul_zero])]
    rw [← hx, form_degreeProj, ← partWord_value]
    have hd : degree (partWord (ydOf ⇑g hg).rowLens) ≠ n := by
      rw [partWord_degree, EKIntegralBases.rowLens_sum, ← card_toMultiset_antitone g hg]
      exact hc
    rw [degreeProj_basis, if_neg hd, map_zero]

end OddMath.Frontier.EKGeneralQ
