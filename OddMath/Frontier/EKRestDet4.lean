import OddMath.Frontier.EKRestRibbon

/-! # The Gram determinant via the basis `h̃_α`; degree 4

EK arXiv:1107.5610v2, §5.2, pp. 39–40 (minimal polynomials of the degeneracy values of the
form at unspecialised `q`, with multiplicities), at arbitrary `q` in any commutative ring `k`.

Compositions of `n` are indexed by their cut sets (`Cut n`, subsets of `{1, …, n-1}`), as in
`EKRestRibbon`.

* `det_gramH_eq`: the Gram determinant of (2.1) in the basis `h_α` equals that in the basis
  `h̃_α` of (2.31), for every `n` (the change of basis is unitriangular: its inverse is the
  inclusion matrix, `mobU_mul_zeta`).
* `det_gramH_four`: in degree 4,
  `det = q¹⁷ (q - 1)⁴ (q + 1)⁴ (q⁶ + 2q⁴ - q³ + 2q² + 1)`.
  This is the degree-4 entry of the list on pp. 39–40: the new factor
  `q⁶ + 2q⁴ - q³ + 2q² + 1` with multiplicity `(4,1)`, and multiplicities `(4,17)`, `(4,4)`,
  `(4,4)` of `q`, `q - 1`, `q + 1`. (Irreducibility of the sextic is not formalized.)

* `example_2_19`: EK Example 2.19 (p. 22), `(h₃₁, h₂₂) = 1 + q²`, `(h̃₃₁, h̃₂₂) = q²`.
* `mobU_mul_zeta`: the change of basis `h ↦ h̃` of (2.31) is invertible over `ℤ` (p. 22:
  "upper-triangular and unimodular"), with inverse the inclusion matrix.

Method for degree 4: by (2.33) (`EKRestRibbon.eq_2_33`) the Gram matrix in the basis `h̃_α`
has entries `Σ_{C(σ)=α, C(σ⁻¹)=β} q^{ℓ(σ)}`; the counts of permutations of `S₄` by
descent sets and length are checked by kernel reduction, and the resulting sparse `8 × 8`
determinant is expanded directly.
-/

noncomputable section
open scoped BigOperators

namespace OddMath.Frontier.EKRest
open EKGeneralQ EKPlatformBijection

variable {k : Type*} [CommRing k] (q : k)

/-- Cut sets of compositions of `n`: subsets of `{1, …, n-1}`. -/
abbrev Cut (n : ℕ) := {S : Finset (Fin n) // ∀ s ∈ S, 0 < s.val}

/-- The Gram matrix of (2.1) in the basis `h_α`. -/
def gramH (n : ℕ) : Matrix (Cut n) (Cut n) k := fun S R => form q (hS (k := k) S.1) (hS R.1)

/-- The Gram matrix of (2.1) in the basis `h̃_α`. -/
def gramHt (n : ℕ) : Matrix (Cut n) (Cut n) k := fun S R => form q (hT (k := k) S.1) (hT R.1)

/-- The change of basis `h ↦ h̃` of (2.31). -/
def mobU (n : ℕ) : Matrix (Cut n) (Cut n) ℤ :=
  fun S T => if T.1 ⊆ S.1 then (-1 : ℤ) ^ (S.1.card - T.1.card) else 0

/-- The inclusion (zeta) matrix. -/
def zeta (n : ℕ) : Matrix (Cut n) (Cut n) ℤ := fun S T => if T.1 ⊆ S.1 then 1 else 0

theorem sum_cut_subset {n : ℕ} {M : Type*} [AddCommMonoid M] (S : Cut n)
    (f : Finset (Fin n) → M) :
    ∑ T : Cut n, (if T.1 ⊆ S.1 then f T.1 else 0) = ∑ T ∈ S.1.powerset, f T := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun T _ => T.1)
  · intro T hT
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hT).2
  · intro T _ T' _ h; exact Subtype.ext h
  · intro T hT
    have hT' := Finset.mem_powerset.mp hT
    exact ⟨⟨T, fun s hs => S.2 s (hT' hs)⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩, rfl⟩
  · intro T _; rfl

theorem hT_eq_sum {n : ℕ} (S : Cut n) :
    hT (k := k) S.1 = ∑ T : Cut n, mobU n S T • hS (k := k) T.1 := by
  rw [hT, ← sum_cut_subset S (fun T => ((-1 : ℤ) ^ (S.1.card - T.card)) • hS (k := k) T)]
  apply Finset.sum_congr rfl
  intro T _
  simp only [mobU]
  split_ifs <;> simp

theorem mobU_mul_zeta (n : ℕ) : mobU n * zeta n = 1 := by
  classical
  ext S R
  rw [Matrix.mul_apply]
  have h := incl_excl S.1 R.1
  rw [← sum_cut_subset S (fun T => (-1 : ℤ) ^ (S.1.card - T.card) * (if R.1 ⊆ T then 1 else 0))] at h
  have e : ∀ T : Cut n, mobU n S T * zeta n T R =
      (if T.1 ⊆ S.1 then (-1 : ℤ) ^ (S.1.card - T.1.card) * (if R.1 ⊆ T.1 then 1 else 0) else 0) := by
    intro T; simp only [mobU, zeta]; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun T _ => e T), h, Matrix.one_apply]
  by_cases hRS : R = S
  · subst hRS; simp
  · rw [if_neg (fun h => hRS (Subtype.ext h)), if_neg (Ne.symm hRS)]

theorem det_mobU_sq (n : ℕ) : (mobU n).det ^ 2 = 1 := by
  have h := congrArg Matrix.det (mobU_mul_zeta n)
  rw [Matrix.det_mul, Matrix.det_one] at h
  rcases Int.isUnit_iff.mp (isUnit_of_mul_eq_one _ _ h) with h1 | h1 <;> rw [h1] <;> norm_num

theorem gramHt_eq (n : ℕ) :
    gramHt q n = (mobU n).map (Int.cast : ℤ → k) * gramH q n *
      ((mobU n).map (Int.cast : ℤ → k)).transpose := by
  ext S R
  simp only [gramHt, gramH, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [hT_eq_sum S, hT_eq_sum R]
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply]
  simp only [zsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro T _
  apply Finset.sum_congr rfl; intro T' _
  ring

/-- **The Gram determinant in the bases `h_α` and `h̃_α` coincide** (every `n`, any `k`, `q`). -/
theorem det_gramH_eq (n : ℕ) : (gramH q n).det = (gramHt q n).det := by
  rw [gramHt_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hU : ((mobU n).map (Int.cast : ℤ → k)).det = ((mobU n).det : k) :=
    ((Int.castRingHom k).map_det (mobU n)).symm
  have h2 : (((mobU n).det : ℤ) : k) ^ 2 = 1 := by
    rw [← Int.cast_pow, det_mobU_sq]; simp
  rw [hU]
  linear_combination -(gramH q n).det * h2

/-! ## Degree 4 -/

/-- The eight cut sets of compositions of `4`, in the order
`∅, {1}, {2}, {3}, {1,2}, {1,3}, {2,3}, {1,2,3}` (i.e. `4, 13, 22, 31, 112, 121, 211, 1111`). -/
def cutList : Fin 8 → Cut 4 := ![⟨∅, by decide⟩, ⟨{1}, by decide⟩, ⟨{2}, by decide⟩,
  ⟨{3}, by decide⟩, ⟨{1, 2}, by decide⟩, ⟨{1, 3}, by decide⟩, ⟨{2, 3}, by decide⟩,
  ⟨{1, 2, 3}, by decide⟩]

def cutEquiv : Fin 8 ≃ Cut 4 := Equiv.ofBijective cutList (by decide)

/-- The compositions encoded by `cutList`: `4, 13, 22, 31, 112, 121, 211, 1111`. -/
theorem parts_cutList : ∀ i : Fin 8, List.ofFn (parts (cutList i).1) =
    ![[4], [1, 3], [2, 2], [3, 1], [1, 1, 2], [1, 2, 1], [2, 1, 1], [1, 1, 1, 1]] i := by
  decide

/-- Numbers of `σ ∈ S₄` with `Des σ⁻¹ = cutList i`, `Des σ = cutList j`, `ℓ(σ) = t`. -/
def cnt4 : Fin 8 → Fin 8 → Fin 7 → ℕ :=
  ![![![1,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0]],
  ![![0,0,0,0,0,0,0], ![0,1,0,0,0,0,0], ![0,0,1,0,0,0,0], ![0,0,0,1,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0]],
  ![![0,0,0,0,0,0,0], ![0,0,1,0,0,0,0], ![0,1,0,0,1,0,0], ![0,0,1,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,1,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0]],
  ![![0,0,0,0,0,0,0], ![0,0,0,1,0,0,0], ![0,0,1,0,0,0,0], ![0,1,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0]],
  ![![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,1,0,0,0], ![0,0,0,0,1,0,0], ![0,0,0,0,0,1,0], ![0,0,0,0,0,0,0]],
  ![![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,1,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,1,0,0], ![0,0,1,0,0,1,0], ![0,0,0,0,1,0,0], ![0,0,0,0,0,0,0]],
  ![![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,1,0], ![0,0,0,0,1,0,0], ![0,0,0,1,0,0,0], ![0,0,0,0,0,0,0]],
  ![![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,0], ![0,0,0,0,0,0,1]]]

theorem inversions_lt (σ : Equiv.Perm (Fin 4)) : inversions σ < 7 := by
  revert σ; decide

theorem cnt4_spec : ∀ i j : Fin 8, ∀ t : Fin 7,
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) =>
      Des σ = (cutList j).1 ∧ Des σ⁻¹ = (cutList i).1 ∧ inversions σ = t)).card = cnt4 i j t := by
  decide

open Classical in
theorem gramHt_four (i j : Fin 8) :
    gramHt q 4 (cutList i) (cutList j) = ∑ t : Fin 7, (cnt4 i j t : k) * q ^ (t : ℕ) := by
  rw [gramHt, eq_2_33]
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : Equiv.Perm (Fin 4) =>
    (⟨inversions σ, inversions_lt σ⟩ : Fin 7))]
  apply Finset.sum_congr rfl
  intro t _
  rw [← cnt4_spec i j t, Finset.sum_filter, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h1 : Des σ = (cutList j).1 <;> by_cases h2 : Des σ⁻¹ = (cutList i).1 <;>
    by_cases h3 : inversions σ = t <;> simp [h1, h2, h3, Fin.ext_iff]

/-- The Gram matrix of (2.1) in the basis `h̃_α`, degree 4, in the order of `cutList`. -/
def gramHt4 : Matrix (Fin 8) (Fin 8) k := !![
  1, 0, 0, 0, 0, 0, 0, 0;
  0, q, q^2, q^3, 0, 0, 0, 0;
  0, q^2, q^4 + q, q^2, 0, q^3, 0, 0;
  0, q^3, q^2, q, 0, 0, 0, 0;
  0, 0, 0, 0, q^3, q^4, q^5, 0;
  0, 0, q^3, 0, q^4, q^5 + q^2, q^4, 0;
  0, 0, 0, 0, q^5, q^4, q^3, 0;
  0, 0, 0, 0, 0, 0, 0, q^6]

theorem gramHt_four_eq : (gramHt q 4).submatrix cutEquiv cutEquiv = gramHt4 q := by
  ext i j
  simp only [Matrix.submatrix_apply, cutEquiv, Equiv.ofBijective_apply, gramHt_four]
  fin_cases i <;> fin_cases j <;> simp [cnt4, gramHt4, Fin.sum_univ_succ] <;> ring

/-! ### The sparse determinant, by blocks -/

section blocks
open Matrix

/-- Two-part block (cut sets `{1}, {3}, {2}`). -/
def blkA : Matrix (Fin 3) (Fin 3) k := !![q, q^3, q^2; q^3, q, q^2; q^2, q^2, q^4 + q]
/-- Three-part block (cut sets `{1,3}, {1,2}, {2,3}`). -/
def blkB : Matrix (Fin 3) (Fin 3) k := !![q^5 + q^2, q^4, q^4; q^4, q^3, q^5; q^4, q^5, q^3]
/-- The coupling `({2}, {1,3})`. -/
def blkC : Matrix (Fin 3) (Fin 3) k := !![0, 0, 0; 0, 0, 0; q^3, 0, 0]
def blkD : Matrix (Fin 3) (Fin 3) k := !![0, 0, q^3; 0, 0, 0; 0, 0, 0]

def M6 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k := fromBlocks (blkA q) (blkC q) (blkD q) (blkB q)

theorem det_M6 : (M6 q).det = (blkA q).det * (blkB q).det - q ^ 6 * (q^2 - q^6) * (q^6 - q^10) := by
  classical
  -- split the row `{2}` into its `A`-part and its coupling part
  let u : Fin 3 ⊕ Fin 3 → k := Sum.elim (blkA q 2) 0
  let w : Fin 3 ⊕ Fin 3 → k := Sum.elim 0 (blkC q 2)
  have hrow : M6 q (Sum.inl 2) = u + w := by
    funext j; rcases j with j | j <;> fin_cases j <;> simp [M6, u, w, blkA, blkC]
  have e1 : updateRow (M6 q) (Sum.inl 2) u = fromBlocks (blkA q) 0 (blkD q) (blkB q) := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [M6, u, updateRow_apply, blkA, blkB, blkC, blkD]
  -- in the coupling part, split the row `{1,3}`
  obtain ⟨N, hN⟩ : ∃ N, N = updateRow (M6 q) (Sum.inl 2) w := ⟨_, rfl⟩
  let u' : Fin 3 ⊕ Fin 3 → k := Sum.elim (blkD q 0) 0
  let w' : Fin 3 ⊕ Fin 3 → k := Sum.elim 0 (blkB q 0)
  have hrow' : N (Sum.inr 0) = u' + w' := by
    funext j; rcases j with j | j <;> fin_cases j <;>
      simp [hN, M6, u', w', w, updateRow_apply, blkB, blkD, blkC]
  have e2 : updateRow N (Sum.inr 0) w' =
      fromBlocks (!![q, q^3, q^2; q^3, q, q^2; 0, 0, 0]) (blkC q) 0 (blkB q) := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [hN, M6, w', w, updateRow_apply, blkA, blkB, blkC, blkD]
  obtain ⟨P, hP0⟩ : ∃ P, P = updateRow N (Sum.inr 0) u' := ⟨_, rfl⟩
  have e3 : P.submatrix (Equiv.swap (Sum.inl 2) (Sum.inr 0)) id =
      fromBlocks (!![q, q^3, q^2; q^3, q, q^2; 0, 0, q^3]) 0 0
        (!![q^3, 0, 0; q^4, q^3, q^5; q^4, q^5, q^3]) := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [hP0, hN, M6, u', w, updateRow_apply, Equiv.swap_apply_def, blkA, blkB, blkC, blkD]
  have hP : P.det = -((!![q, q^3, q^2; q^3, q, q^2; 0, 0, q^3] : Matrix (Fin 3) (Fin 3) k).det *
      (!![q^3, 0, 0; q^4, q^3, q^5; q^4, q^5, q^3] : Matrix (Fin 3) (Fin 3) k).det) := by
    have := det_permute (Equiv.swap (Sum.inl (2 : Fin 3)) (Sum.inr (0 : Fin 3))) P
    rw [e3, det_fromBlocks_zero₂₁, Equiv.Perm.sign_swap (by simp)] at this
    rw [this]; simp
  rw [← updateRow_eq_self (M6 q) (Sum.inl 2), hrow, det_updateRow_add, e1, det_fromBlocks_zero₁₂,
    ← hN, ← updateRow_eq_self N (Sum.inr 0), hrow', det_updateRow_add, e2, det_fromBlocks_zero₂₁,
    ← hP0, hP]
  simp [det_fin_three]
  ring

end blocks

/-- **EK §5.2, pp. 39–40, degree 4:** the Gram determinant of the form (2.1) on `Λ′₄` is
`q¹⁷ (q - 1)⁴ (q + 1)⁴ (q⁶ + 2q⁴ - q³ + 2q² + 1)`. -/
theorem det_gramH_four :
    (gramH q 4).det = q ^ 17 * (q - 1) ^ 4 * (q + 1) ^ 4 * (q^6 + 2 * q^4 - q^3 + 2 * q^2 + 1) := by
  let f : (Fin 3 ⊕ Fin 3) ⊕ Fin 2 → Fin 8 :=
    Sum.elim (Sum.elim ![1, 3, 2] ![5, 4, 6]) ![0, 7]
  have hf : Function.Bijective f := by decide
  let e := Equiv.ofBijective f hf
  have hsub : (gramHt4 q).submatrix e e =
      Matrix.fromBlocks (M6 q) 0 0 (!![1, 0; 0, q^6] : Matrix (Fin 2) (Fin 2) k) := by
    ext ((i | i) | i) ((j | j) | j) <;> fin_cases i <;> fin_cases j <;>
      simp [e, f, gramHt4, M6, blkA, blkB, blkC, blkD]
  rw [det_gramH_eq, ← Matrix.det_submatrix_equiv_self cutEquiv, gramHt_four_eq,
    ← Matrix.det_submatrix_equiv_self e, hsub, Matrix.det_fromBlocks_zero₂₁, det_M6]
  simp [blkA, blkB, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

/-! ## Example 2.19 (p. 22) -/

open Classical in
theorem form_hS_four (i j : Fin 8) (c : Fin 7 → ℕ)
    (hc : ∀ t : Fin 7, (Finset.univ.filter (fun σ : Equiv.Perm (Fin 4) =>
      Des σ ⊆ (cutList j).1 ∧ Des σ⁻¹ ⊆ (cutList i).1 ∧ inversions σ = t)).card = c t) :
    form q (hS (k := k) (cutList i).1) (hS (cutList j).1) = ∑ t : Fin 7, (c t : k) * q ^ (t : ℕ) := by
  rw [form_hS]
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : Equiv.Perm (Fin 4) =>
    (⟨inversions σ, inversions_lt σ⟩ : Fin 7))]
  apply Finset.sum_congr rfl
  intro t _
  rw [← hc t, Finset.sum_filter, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h1 : Des σ ⊆ (cutList j).1 <;> by_cases h2 : Des σ⁻¹ ⊆ (cutList i).1 <;>
    by_cases h3 : inversions σ = t <;> simp [h1, h2, h3, Fin.ext_iff]

/-- **EK Example 2.19, p. 22:** `(h₃₁, h₂₂) = 1 + q²` and `(h̃₃₁, h̃₂₂) = q²`
(`cutList 3 = {3}` encodes `31`, `cutList 2 = {2}` encodes `22`). -/
theorem example_2_19 :
    form q (hS (k := k) (cutList 3).1) (hS (cutList 2).1) = 1 + q ^ 2 ∧
      form q (hT (k := k) (cutList 3).1) (hT (cutList 2).1) = q ^ 2 := by
  constructor
  · rw [form_hS_four q 3 2 ![1, 0, 1, 0, 0, 0, 0] (by decide)]
    simp [Fin.sum_univ_succ]
  · have := gramHt_four q 3 2
    rw [gramHt] at this
    rw [this]
    simp [cnt4, Fin.sum_univ_succ]

end OddMath.Frontier.EKRest
