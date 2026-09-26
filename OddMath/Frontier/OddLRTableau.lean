import OddMath.Frontier.OddGrassmannSchur
import OddMath.Frontier.TableauDominance
import OddMath.Frontier.TableauStripSigns

/-!
# Skew tableaux, Yamanouchi words, LR tableaux, and odd LR coefficients

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E").

* E §4.1, p.12: skew shape `λ/μ` (complement of a subdiagram `μ ⊆ λ`), semistandard skew
  tableaux `SSYT(λ/μ, ν)`, Yamanouchi (reverse lattice) words, Littlewood–Richardson tableaux.
* E §4.2, p.13: `sign(S) = sign(Ŝ)`, where `Ŝ` fills `μ` with a letter `j` below every entry
  of `S` (here `j = 0`, E Example 4.4). The printed display reads `sign(Ŝ) = N^<(Ŝ)`; the
  intended value, used in Example 4.4 and Theorem 4.8, is `(-1)^{N^<(Ŝ)}`.
* E §4.2, p.13: `sign(Y, Z)` for monomials with `Y = ±Z`.
* E Definition 4.6, p.13: the odd Littlewood–Richardson coefficient `c^λ_{μν}`, the
  `s_λ`-coordinate of `s_μ s_ν` in `OΛ`, here EK's `Q` with the basis
  `OddGrassmannSchur.sBasis` of the `s^K_λ = OddLREKIdentification.sK λ`.

Conventions: English zero-based cells `(row, column)`, positive letters, row words read left to
right and bottom to top (`TableauRowWord.rowCells`). `N(λ) = TableauStripSigns.north λ` and
`dN(λ) = TableauStripSigns.directNorth λ` (E §2.2); `sign(T_λ) = (-1)^{N(λ)}` is
`CompleteTableauExpansion.canonical_sign`.
-/

namespace OddMath.Frontier.OddLRTableau

open TableauSign TableauRowWord
open scoped BigOperators

/-! ## Skew shapes and skew tableaux -/

/-- The cells of the skew shape `λ/μ`. -/
def skewCells (lam mu : YoungDiagram) : Finset (ℕ × ℕ) := lam.cells \ mu.cells

theorem mem_skewCells {lam mu : YoungDiagram} {p : ℕ × ℕ} :
    p ∈ skewCells lam mu ↔ p ∈ lam ∧ p ∉ mu := by
  simp [skewCells]

/-- A semistandard skew tableau of shape `λ/μ` (E §4.1, p.12): `μ ⊆ λ`, positive entries on
`λ/μ`, weakly increasing along rows, strictly increasing down columns; `0` elsewhere (so the
entry function is E's `Ŝ` with `j = 0`). -/
structure SkewTableau (lam mu : YoungDiagram) where
  entry : ℕ → ℕ → ℕ
  sub : mu ≤ lam
  row_weak : ∀ {i j₁ j₂ : ℕ}, j₁ < j₂ → (i, j₂) ∈ lam → (i, j₁) ∉ mu →
    entry i j₁ ≤ entry i j₂
  col_strict : ∀ {i₁ i₂ j : ℕ}, i₁ < i₂ → (i₂, j) ∈ lam → (i₁, j) ∉ mu →
    entry i₁ j < entry i₂ j
  zeros_out : ∀ {i j : ℕ}, (i, j) ∉ lam → entry i j = 0
  zeros_in : ∀ {i j : ℕ}, (i, j) ∈ mu → entry i j = 0
  positive : ∀ {i j : ℕ}, (i, j) ∈ lam → (i, j) ∉ mu → 0 < entry i j

namespace SkewTableau

variable {lam mu : YoungDiagram}

theorem ext' {S T : SkewTableau lam mu} (h : ∀ i j, S.entry i j = T.entry i j) : S = T := by
  cases S; cases T
  simp only [mk.injEq]
  funext i j
  exact h i j

/-- A skew tableau is determined by its entries on `λ/μ`. -/
theorem ext_skew {S T : SkewTableau lam mu}
    (h : ∀ p ∈ skewCells lam mu, S.entry p.1 p.2 = T.entry p.1 p.2) : S = T := by
  apply ext'
  intro i j
  by_cases hl : (i, j) ∈ lam
  · by_cases hm : (i, j) ∈ mu
    · rw [S.zeros_in hm, T.zeros_in hm]
    · exact h (i, j) (mem_skewCells.mpr ⟨hl, hm⟩)
  · rw [S.zeros_out hl, T.zeros_out hl]

/-- Content: multiplicity of each letter on `λ/μ`. -/
noncomputable def content (S : SkewTableau lam mu) : ℕ →₀ ℕ :=
  ∑ p ∈ skewCells lam mu, Finsupp.single (S.entry p.1 p.2) 1

theorem content_apply (S : SkewTableau lam mu) (k : ℕ) :
    S.content k = ((skewCells lam mu).filter (fun p => S.entry p.1 p.2 = k)).card := by
  classical
  simp only [content, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.card_filter]

theorem entry_mem_support (S : SkewTableau lam mu) {p : ℕ × ℕ} (hp : p ∈ skewCells lam mu) :
    S.entry p.1 p.2 ∈ S.content.support := by
  classical
  rw [Finsupp.mem_support_iff, content_apply]
  exact Finset.card_ne_zero.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩

/-- Row word `w_r(S)` (E §2.1, §4.1): left to right, bottom to top, over `λ/μ` only. -/
noncomputable def rowWord (S : SkewTableau lam mu) : List ℕ :=
  ((rowCells lam).filter (fun p => p ∉ mu.cells)).map (fun p => S.entry p.1 p.2)

/-- Row word of `Ŝ` (E §4.2, p.13): the whole of `λ`, with the letter `0` on `μ`. -/
noncomputable def hatWord (S : SkewTableau lam mu) : List ℕ :=
  (rowCells lam).map (fun p => S.entry p.1 p.2)

/-- `N^<(Ŝ)`: the number of inversions of the row word of `Ŝ`, i.e. of pairs of boxes with the
northern one carrying the smaller entry (E §2.2 and §4.2; `TableauRowWord.rowWord_inversions`). -/
noncomputable def Nlt (S : SkewTableau lam mu) : ℕ := inversions S.hatWord

/-- `sign(S) = sign(Ŝ) = (-1)^{N^<(Ŝ)}` (E §4.2, p.13). -/
noncomputable def sign (S : SkewTableau lam mu) : ℤ := (-1 : ℤ) ^ S.Nlt

/-! ### Finiteness of fixed-content skew tableaux -/

/-- Encoding of a fixed-content skew tableau by its values on `λ/μ`. -/
noncomputable def encode (c : ℕ →₀ ℕ) (S : {S : SkewTableau lam mu // S.content = c}) :
    skewCells lam mu → c.support := fun p =>
  ⟨S.1.entry p.1.1 p.1.2, by simpa only [S.2] using S.1.entry_mem_support p.2⟩

theorem encode_injective (c : ℕ →₀ ℕ) : Function.Injective (encode (lam := lam) (mu := mu) c) := by
  intro S T h
  apply Subtype.ext
  apply ext_skew
  intro p hp
  have := congrArg (fun f => (f ⟨p, hp⟩ : ℕ)) h
  simpa [encode] using this

noncomputable instance (c : ℕ →₀ ℕ) : Fintype {S : SkewTableau lam mu // S.content = c} := by
  classical
  exact Fintype.ofInjective _ (encode_injective c)

end SkewTableau

/-- `SSYT(λ/μ, c)` as a finite set. -/
noncomputable def ofContent (lam mu : YoungDiagram) (c : ℕ →₀ ℕ) :
    Finset (SkewTableau lam mu) :=
  Finset.univ.map (Function.Embedding.subtype fun S : SkewTableau lam mu => S.content = c)

theorem mem_ofContent {lam mu : YoungDiagram} {c : ℕ →₀ ℕ} {S : SkewTableau lam mu} :
    S ∈ ofContent lam mu c ↔ S.content = c := by
  constructor
  · intro h
    obtain ⟨T, -, rfl⟩ := Finset.mem_map.mp h
    exact T.2
  · intro h
    exact Finset.mem_map.mpr ⟨⟨S, h⟩, Finset.mem_univ _, rfl⟩

/-! ## Yamanouchi words and LR tableaux -/

/-- Yamanouchi (reverse lattice) word, E §4.1, p.12: read backwards, every initial subword has
at least as many `a`s as `b`s whenever `a < b` (positive alphabet). -/
def Yamanouchi (w : List ℕ) : Prop :=
  ∀ t, t <:+ w → ∀ a b : ℕ, 0 < a → a < b → t.count b ≤ t.count a

/-- A Littlewood–Richardson tableau: a skew tableau with Yamanouchi row word (E §4.1, p.12). -/
def IsLR {lam mu : YoungDiagram} (S : SkewTableau lam mu) : Prop := Yamanouchi S.rowWord

/-- LR tableaux of shape `λ/μ` and content `ν` (letter `i+1` occurs `ν_{i+1}` times). -/
noncomputable def lrTableaux (lam mu nu : YoungDiagram) : Finset (SkewTableau lam mu) := by
  classical
  exact (ofContent lam mu (TableauDominance.shapeContent nu)).filter IsLR

theorem mem_lrTableaux {lam mu nu : YoungDiagram} {S : SkewTableau lam mu} :
    S ∈ lrTableaux lam mu nu ↔ S.content = TableauDominance.shapeContent nu ∧ IsLR S := by
  classical
  unfold lrTableaux
  rw [Finset.mem_filter, mem_ofContent]

/-! ## `sign(Y, Z)` and the odd LR coefficient -/

/-- `sign(Y, Z)` (E §4.2, p.13): the sign `ε` with `Y = ε Z`, for nonzero `Y = ±Z`
(and `0` when `Y ≠ ±Z`). -/
noncomputable def signBetween {M : Type*} [AddCommGroup M] (Y Z : M) : ℤ := by
  classical
  exact if Y = Z then 1 else if Y = -Z then -1 else 0

/-- E Definition 4.6, p.13: `c^λ_{μν}`, the coefficient of `s_λ` in `s_μ s_ν` in the basis of odd
Schur functions of `OΛ`. -/
noncomputable def oddLR (lam mu nu : YoungDiagram) : ℤ :=
  OddGrassmannSchur.sBasis.repr (OddLREKIdentification.sK mu * OddLREKIdentification.sK nu) lam

/-- The expansion defining `c^λ_{μν}`: `s_μ s_ν = Σ_λ c^λ_{μν} s_λ` (finite support). -/
theorem sK_mul_sK_eq (mu nu : YoungDiagram) :
    OddLREKIdentification.sK mu * OddLREKIdentification.sK nu =
      (OddGrassmannSchur.sBasis.repr
        (OddLREKIdentification.sK mu * OddLREKIdentification.sK nu)).sum
        (fun lam c => c • OddLREKIdentification.sK lam) := by
  conv_lhs => rw [← OddGrassmannSchur.sBasis.linearCombination_repr
    (OddLREKIdentification.sK mu * OddLREKIdentification.sK nu)]
  simp [Finsupp.linearCombination_apply]

/-- `c^λ_{μν}` is the unique family of coordinates. -/
theorem oddLR_unique (mu nu : YoungDiagram) (c : YoungDiagram →₀ ℤ)
    (h : OddLREKIdentification.sK mu * OddLREKIdentification.sK nu =
      c.sum (fun lam a => a • OddLREKIdentification.sK lam)) (lam : YoungDiagram) :
    oddLR lam mu nu = c lam := by
  unfold oddLR
  rw [h]
  have : c.sum (fun lam a => a • OddLREKIdentification.sK lam) =
      Finsupp.linearCombination ℤ OddGrassmannSchur.sBasis c := by
    simp [Finsupp.linearCombination_apply]
  rw [this, OddGrassmannSchur.sBasis.repr_linearCombination]

/-- The right-hand side of E (4.6): `(-1)^{N(μ)+N(λ)} Σ_{S LR, shape λ/μ, content ν} (-1)^{N^<(S)}`. -/
noncomputable def lrSignedCount (lam mu nu : YoungDiagram) : ℤ :=
  (-1 : ℤ) ^ (TableauStripSigns.north mu + TableauStripSigns.north lam) *
    ∑ S ∈ lrTableaux lam mu nu, S.sign

end OddMath.Frontier.OddLRTableau
