import OddMath.Frontier.OddGrassmannSchur
import OddMath.Frontier.OddLRVerticalPieri
import OddMath.Frontier.EKOddRSKII
import OddMath.Frontier.TableauStripCorners

/-! EKL arXiv:1111.1320v1, §2.3, Remark 2.27, display (2.72), p.19–20.

The first of the three further Pieri rules,
`(-1)^{ℓ(w_α)} s_α s_{(k)} = Σ_μ (-1)^{ℓ(w_μ)} (-1)^{|i₁/ᾱ| + ⋯ + |i_k/ᾱ|} s_μ`
(sum over `μ ⊃ α` with `μ/α` a horizontal strip, `i_j` the columns receiving a box), is
proved in `OΛ` (EK's `Q`) for EK's Schur functions `s^H`, and in every `OΛ_a` for the odd Schur
polynomials of Definition 2.24 (shapes with more than `a` rows contribute `0`). The source
assumes Conjecture 5.3, available here as `OddGrassmannSchur.conjecture_5_3`.
`ℓ(w_λ)` is EK's northeast/southwest pair count `EKSemiorthogonality.ell`.
The route is the one indicated in the Remark: the vertical rule (2.71), lifted to `OΛ`,
transported by EK's `ψ₁ψ₂`, which acts by `s_λ ↦ (-1)^{ℓ(w_λ)+|λ|} s_{λᵀ}` (EK Lemma 3.11). -/
namespace OddMath.Frontier.EKLSectionTwo
open EKRadicalQuotient (Q)
open OddLREKIdentification (piN sK)
open DegreeShapes (DegreeShape degreeFintype)
open OddLRVerticalPieri (Vertical stripBelow belowCount column)
open TableauStripCorners (Horizontal)
open EKSemiorthogonality (ell)
open scoped BigOperators
noncomputable section
set_option synthInstance.maxHeartbeats 200000
attribute [local instance] Classical.propDecidable

/-- An element of `OΛ` vanishing in every `OΛ_N` is zero. -/
theorem eq_zero_of_piN (x : Q) (h : ∀ N, piN N x = 0) : x = 0 := by
  classical
  set c := EKIntegralBases.eBasis.repr x
  let N := ∑ μ ∈ c.support, μ.rowLen 0
  have hw := OddSymmetricLimit.mem_wideSpan_of_piN_eq_zero (h N)
  have hs : OddSymmetricLimit.wideSpan N =
      Submodule.span ℤ (EKIntegralBases.eBasis '' {μ | N < μ.rowLen 0}) := by
    unfold OddSymmetricLimit.wideSpan
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image, EKIntegralBases.eBasis_apply]
    constructor
    · rintro ⟨μ, hμ, rfl⟩; exact ⟨μ, hμ, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩; exact ⟨μ, hμ, rfl⟩
  rw [hs, Basis.mem_span_image] at hw
  have hc : c = 0 := by
    ext μ
    by_contra hne
    have hmem : μ ∈ c.support := Finsupp.mem_support_iff.mpr hne
    have h1 := hw hmem
    have h2 : μ.rowLen 0 ≤ N :=
      Finset.single_le_sum (f := fun μ : YoungDiagram => μ.rowLen 0) (fun _ _ => Nat.zero_le _) hmem
    exact absurd h1 (not_lt.mpr h2)
  have hc' : EKIntegralBases.eBasis.repr x = 0 := hc
  exact EKIntegralBases.eBasis.repr.injective (by rw [hc', map_zero])

/-- (2.71) lifted to `OΛ`: `s_λ s_{(1^k)} = Σ_{μ/λ vertical} (-1)^{|i₁/λ|+⋯+|i_k/λ|} s_μ`. -/
theorem vertical_pieri_Q (lam : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (lam.card + k)
    sK lam * sK (column k) =
      ∑ mu : DegreeShape (lam.card + k), if Vertical lam mu.val then
        (-1 : ℤ) ^ stripBelow lam mu.val • sK mu.val else 0 := by
  letI := degreeFintype (lam.card + k)
  rw [← sub_eq_zero]
  apply eq_zero_of_piN
  intro N
  rw [map_sub, map_mul, map_sum, OddLREKIdentification.piN_sK, OddLREKIdentification.piN_sK,
    OddLRVerticalPieri.vertical_pieri, sub_eq_zero]
  refine Finset.sum_congr rfl fun mu _ => ?_
  split_ifs
  · rw [map_zsmul, OddLREKIdentification.piN_sK]
  · rw [map_zero]

/-! ### Transposition -/

/-- `|i/ᾱ|` for the column `c` of `α`: boxes of `α` strictly right of column `c`. -/
def rightCount (α : YoungDiagram) (c : ℕ) : ℕ := (α.cells.filter (fun q => c < q.2)).card

/-- The printed exponent `|i₁/ᾱ| + ⋯ + |i_k/ᾱ|`, one term per box of `μ/α`. -/
def stripRight (α μ : YoungDiagram) : ℕ := ∑ p ∈ μ.cells \ α.cells, rightCount α p.2

theorem cells_transpose (μ : YoungDiagram) :
    μ.transpose.cells = μ.cells.map (Equiv.prodComm ℕ ℕ).toEmbedding := by
  change (Equiv.prodComm ℕ ℕ).finsetCongr μ.cells = _
  rw [Equiv.finsetCongr_apply]

theorem mem_transpose_cells (μ : YoungDiagram) (p : ℕ × ℕ) :
    p ∈ μ.transpose.cells ↔ p.swap ∈ μ.cells :=
  YoungDiagram.mem_transpose

theorem vertical_transpose_iff (α μ : YoungDiagram) :
    Vertical α.transpose μ.transpose ↔ Horizontal α μ := by
  unfold Vertical Horizontal
  constructor
  · rintro ⟨hsub, huniq⟩
    refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
    · have := hsub ((mem_transpose_cells α p.swap).mpr (by simpa using hp))
      simpa [mem_transpose_cells] using this
    · simp only [Finset.mem_sdiff, YoungDiagram.mem_cells] at hp hq
      have := huniq p.swap (by simp [Finset.mem_sdiff, mem_transpose_cells, hp.1, hp.2,
          YoungDiagram.mem_cells])
        q.swap (by simp [Finset.mem_sdiff, mem_transpose_cells, hq.1, hq.2, YoungDiagram.mem_cells])
        (by simpa using hpq)
      simpa using congrArg Prod.swap this
  · rintro ⟨hsub, huniq⟩
    refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
    · rw [mem_transpose_cells] at hp ⊢; exact hsub hp
    · simp only [Finset.mem_sdiff, mem_transpose_cells] at hp hq
      have := huniq p.swap (by simp [Finset.mem_sdiff, hp.1, hp.2]) q.swap
        (by simp [Finset.mem_sdiff, hq.1, hq.2]) (by simpa using hpq)
      simpa using congrArg Prod.swap this

theorem stripBelow_transpose (α μ : YoungDiagram) :
    stripBelow α.transpose μ.transpose = stripRight α μ := by
  unfold stripBelow stripRight belowCount rightCount
  refine Finset.sum_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_sdiff, mem_transpose_cells] at hp ⊢; exact hp
  · intro p hp
    simp only [Finset.mem_sdiff, mem_transpose_cells, Prod.swap_swap] at hp ⊢; exact hp
  · intro p _; simp
  · intro p _; simp
  · intro p _
    dsimp only
    rw [cells_transpose, Finset.filter_map, Finset.card_map]
    congr 1

theorem ell_column (k : ℕ) : ell (column k) = 0 := by
  unfold ell
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q hq ⟨_, h2⟩
  rw [OddLRVerticalPieri.mem_column_cells] at hp hq
  omega

theorem card_column (k : ℕ) : (column k).card = k := by
  change ((Finset.range k) ×ˢ ({0} : Finset ℕ)).card = k
  simp

theorem card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  simp [YoungDiagram.card, cells_transpose]

/-- EKL (2.72) in `OΛ`, for every `α` and `k`:
`(-1)^{ℓ(w_α)} s_α s_{(k)} = Σ_{μ/α horizontal} (-1)^{ℓ(w_μ)} (-1)^{|i₁/ᾱ|+⋯+|i_k/ᾱ|} s_μ`,
where `(k)` is the one-row diagram `(1^k)ᵀ`. -/
theorem horizontal_pieri_Q (α : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (α.card + k)
    (-1 : ℤ) ^ ell α • (sK α * sK (column k).transpose) =
      ∑ mu : DegreeShape (α.card + k), if Horizontal α mu.val then
        ((-1 : ℤ) ^ ell mu.val * (-1 : ℤ) ^ stripRight α mu.val) • sK mu.val else 0 := by
  letI := degreeFintype (α.card + k)
  have hv := vertical_pieri_Q α.transpose k
  rw [card_transpose] at hv
  have hp := congrArg EKAutomorphisms.psi12 hv
  rw [map_mul, OddGrassmannSchur.psi12_sK, OddGrassmannSchur.psi12_sK, map_sum] at hp
  simp only [YoungDiagram.transpose_transpose, ell_column, card_column, card_transpose,
    EKOddRSKII.ell_transpose] at hp
  rw [← (EKDualBases.transposeShape (α.card + k)).sum_comp] at hp
  simp only [EKDualBases.transposeShape, Equiv.coe_fn_mk, vertical_transpose_iff] at hp
  have key : ∀ x : DegreeShape (α.card + k), EKAutomorphisms.psi12
      (if Horizontal α x.val then (-1 : ℤ) ^ stripBelow α.transpose x.val.transpose •
        sK x.val.transpose else 0) =
      (-1 : ℤ) ^ (α.card + k) • (if Horizontal α x.val then
        ((-1 : ℤ) ^ ell x.val * (-1 : ℤ) ^ stripRight α x.val) • sK x.val else 0) := by
    intro x
    split_ifs
    · rw [map_zsmul, OddGrassmannSchur.psi12_sK, YoungDiagram.transpose_transpose,
        EKOddRSKII.ell_transpose, card_transpose, x.property, stripBelow_transpose, smul_smul,
        smul_smul]
      congr 1
      ring
    · rw [map_zero, smul_zero]
  simp only [key, ← Finset.smul_sum, smul_mul_smul_comm] at hp
  have h2 := congrArg (fun y : Q => (-1 : ℤ) ^ (α.card + k) • y) hp
  simp only [smul_smul] at h2
  have hsq : ∀ m : ℕ, (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := fun m => by
    rw [← mul_pow]; norm_num
  rw [show (-1 : ℤ) ^ (α.card + k) * ((-1 : ℤ) ^ (ell α + α.card) * (-1 : ℤ) ^ (0 + k)) =
      (-1 : ℤ) ^ ell α * ((-1 : ℤ) ^ (α.card + k) * (-1 : ℤ) ^ (α.card + k)) by
    rw [zero_add, pow_add, pow_add]; ring, hsq, mul_one] at h2
  rwa [one_smul] at h2

/-- The odd Schur polynomial of Definition 2.24 in `OΛ_a`, `a = n+2`, for shapes with at most
`a` rows, and `0` for taller shapes. -/
def schurA (n : ℕ) (μ : YoungDiagram) : OddMath.SkewPolynomial.SkewPolynomial (n+2) :=
  if μ.colLen 0 ≤ n + 2 then OddSymmetrizer.schur n (OddLREKIdentification.toExponent n μ) else 0

theorem piN_sK_eq_schurA (n : ℕ) (μ : YoungDiagram) : piN (n+2) (sK μ) = schurA n μ :=
  OddGrassmannSchur.conjecture_5_3 n μ

/-- EKL (2.72) in `OΛ_a`, for every `a = n+2 ≥ 2`, every `α` and `k`, with the odd Schur
polynomials of Definition 2.24 (`schurA`): shapes with more than `a` rows contribute `0`. -/
theorem horizontal_pieri (n : ℕ) (α : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (α.card + k)
    (-1 : ℤ) ^ ell α • (schurA n α * schurA n (column k).transpose) =
      ∑ mu : DegreeShape (α.card + k), if Horizontal α mu.val then
        ((-1 : ℤ) ^ ell mu.val * (-1 : ℤ) ^ stripRight α mu.val) • schurA n mu.val else 0 := by
  letI := degreeFintype (α.card + k)
  have h := congrArg (piN (n+2)) (horizontal_pieri_Q α k)
  simp only [map_zsmul, map_mul, map_sum, piN_sK_eq_schurA] at h
  rw [h]
  refine Finset.sum_congr rfl fun mu _ => ?_
  split_ifs
  · rw [map_zsmul, piN_sK_eq_schurA]
  · rw [map_zero]

end
end OddMath.Frontier.EKLSectionTwo
