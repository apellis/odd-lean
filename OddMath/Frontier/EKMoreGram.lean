import OddMath.Frontier.EKRestForgotten
import OddMath.Frontier.EKGeneralQNondeg
import OddMath.Frontier.EKRestDegree

/-!
# [EK] §3.1, p. 24, and §5.2, (5.2): determinants and Gram matrices of the bases

Source: A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
arXiv:1107.5610v2. Throughout, `Λ = Q` is the integral radical quotient at `q = −1`, with the
matrices `M_{λμ} = (e_λ, h_μ)`, `M′_{λμ} = (h_λ, h_μ)`, `M″_{λμ} = (e_λ, e_μ)` of (3.2)
(`EKDualBases.M`, `Mh`, `Me`), indexed by all partitions of `d`.

* p. 24: "The determinants `det(M′_n)` and `det(M″_n)` both equal `det(M_n)` times the
  determinant of the change of basis between the e- and h-bases." With `C` the matrix of the
  change of basis `e_λ = Σ_μ C_{λμ} h_μ` and `D` the inverse change `h_λ = Σ_μ D_{λμ} e_μ`:
  `M = C M′`, `M″ = M Cᵀ` (`M_eq_eToH_mul_Mh`, `Me_eq_M_mul_eToH_transpose`),
  `det C = det D = ±1` (`det_eToH_eq_det_hToE`, `det_eToH_sq`), and
  `det M′ = det M · det C = det M · det D`, `det M″ = det M · det C = det M · det D`
  (`det_Mh`, `det_Me`), in every degree.
* p. 24: "the matrix `M⁻¹M′M⁻¹` is the matrix of the bilinear form in the `f`-basis"
  (`gram_f_eq`), in every degree; also `M′ = M G_f M` (`Mh_eq_M_gramF_M`).
* (5.1)–(5.2), pp. 40–41: the natural-number defect `D` of `EKGeneralQ` and the integer defect
  of `EKRest` agree (`degD_cast`), so the Gram determinant of `Λ′_n` over `ℤ[q]` has degree
  exactly `2^{n−2}(n² − 3n + 4) − 1` for every `n ≥ 2` (`gram_det_natDegree_closed`,
  `gram_det_natDegree_closed_nat`).
* p. 25, "`f_n = ±m_n`", at `n = 7`: `m₇ = 4 f₍₄,₃₎ + 8 f₍₅,₂₎ + 5 f₍₇₎` (`m_seven_f_expansion`).
  Hence `m₇` and `f₇` are linearly independent over `ℤ` (`f_seven_m_seven_independent`), so
  `f₇` is not a rational multiple of `m₇` (the `f`-basis is a `ℤ`-basis, so the relation
  `a f₇ = b m₇` with `a, b ∈ ℚ` clears to integers).
-/

noncomputable section
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace OddMath.Frontier.EKMore
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases
open EKPartitionSpanning (hPartition ePartition)

local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-! ## Change of basis between the e- and h-bases -/

/-- `C_{λμ}`: `e_λ = Σ_μ C_{λμ} h_μ` in degree `d`. -/
def eToH (d : ℕ) : Matrix (DegreeShape d) (DegreeShape d) ℤ :=
  fun ν μ => (degreeHBasis d).repr (degreeEBasis d ν) μ

/-- `D_{λμ}`: `h_λ = Σ_μ D_{λμ} e_μ` in degree `d`. -/
def hToE (d : ℕ) : Matrix (DegreeShape d) (DegreeShape d) ℤ :=
  fun ν μ => (degreeEBasis d).repr (degreeHBasis d ν) μ

theorem e_expand (d : ℕ) (ν : DegreeShape d) :
    ePartition ν.val = ∑ μ, eToH d ν μ • hPartition μ.val := by
  have h := congrArg Subtype.val ((degreeHBasis d).sum_repr (degreeEBasis d ν))
  rw [Submodule.coe_sum] at h
  rw [← degreeEBasis_apply, ← h]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Submodule.coe_smul, degreeHBasis_apply]
  rfl

theorem eToH_eq_transpose (d : ℕ) :
    eToH d = ((degreeHBasis d).toMatrix (degreeEBasis d)).transpose := by
  ext ν μ; simp [eToH, Basis.toMatrix_apply]

theorem hToE_eq_transpose (d : ℕ) :
    hToE d = ((degreeEBasis d).toMatrix (degreeHBasis d)).transpose := by
  ext ν μ; simp [hToE, Basis.toMatrix_apply]

theorem det_eToH_mul_det_hToE (d : ℕ) : (eToH d).det * (hToE d).det = 1 := by
  rw [eToH_eq_transpose, hToE_eq_transpose, Matrix.det_transpose, Matrix.det_transpose,
    ← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]

/-- The two changes of basis have the same determinant. -/
theorem det_eToH_eq_det_hToE (d : ℕ) : (eToH d).det = (hToE d).det := by
  have h := det_eToH_mul_det_hToE d
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h with h1 | h1 <;>
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨a, b⟩ | ⟨a, b⟩ <;> omega

theorem det_eToH_sq (d : ℕ) : (eToH d).det * (eToH d).det = 1 := by
  conv_lhs => rw [show (eToH d).det * (eToH d).det = (eToH d).det * (hToE d).det by
    rw [det_eToH_eq_det_hToE]]
  exact det_eToH_mul_det_hToE d

/-- `M = C M′`. -/
theorem M_eq_eToH_mul_Mh (d : ℕ) : M d = eToH d * Mh d := by
  ext ν μ
  rw [Matrix.mul_apply, M, e_expand, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro κ _
  rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul, Mh]

/-- `M″ = M Cᵀ`. -/
theorem Me_eq_M_mul_eToH_transpose (d : ℕ) : Me d = M d * (eToH d).transpose := by
  ext ν μ
  rw [Matrix.mul_apply, Me, e_expand d μ, map_sum]
  apply Finset.sum_congr rfl
  intro κ _
  rw [map_zsmul, smul_eq_mul, Matrix.transpose_apply, M, mul_comm]

/-- [EK] p. 24: `det M′ = det M · det C`, where `C` changes the e-basis into the h-basis. -/
theorem det_Mh (d : ℕ) : (Mh d).det = (M d).det * (eToH d).det := by
  rw [M_eq_eToH_mul_Mh, Matrix.det_mul, mul_comm (eToH d).det, mul_assoc, det_eToH_sq, mul_one]

/-- [EK] p. 24: `det M″ = det M · det C`. -/
theorem det_Me (d : ℕ) : (Me d).det = (M d).det * (eToH d).det := by
  rw [Me_eq_M_mul_eToH_transpose, Matrix.det_mul, Matrix.det_transpose]

/-- [EK] p. 24, all four readings of "the determinant of the change of basis between the e- and
h-bases": `det M′ = det M″ = det M · det C = det M · det D`, and `det C = det D = ±1`. -/
theorem ek_p24_determinants (d : ℕ) :
    (Mh d).det = (M d).det * (eToH d).det ∧ (Mh d).det = (M d).det * (hToE d).det ∧
    (Me d).det = (M d).det * (eToH d).det ∧ (Me d).det = (M d).det * (hToE d).det ∧
    (eToH d).det = (hToE d).det ∧ ((eToH d).det = 1 ∨ (eToH d).det = -1) := by
  refine ⟨det_Mh d, ?_, det_Me d, ?_, det_eToH_eq_det_hToE d,
    Int.eq_one_or_neg_one_of_mul_eq_one (det_eToH_sq d)⟩
  · rw [det_Mh, det_eToH_eq_det_hToE]
  · rw [det_Me, det_eToH_eq_det_hToE]

/-! ## The Gram matrix in the f-basis -/

/-- The Gram matrix of the form in the forgotten basis, `(f_λ, f_μ)`. -/
def gramF (d : ℕ) : Matrix (DegreeShape d) (DegreeShape d) ℤ :=
  fun ν μ => quotientPairing (fBasis d ν : Q) (fBasis d μ : Q)

theorem h_expand_f (d : ℕ) (ν : DegreeShape d) :
    hPartition ν.val = ∑ μ, M d ν μ • (fBasis d μ : Q) := by
  have h := congrArg Subtype.val (h_eq_M_f d ν)
  rw [degreeHBasis_apply, Submodule.coe_sum] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Submodule.coe_smul]

/-- `M′ = M G_f M` (using `M = Mᵀ`). -/
theorem Mh_eq_M_gramF_M (d : ℕ) : Mh d = M d * gramF d * M d := by
  ext ν μ
  rw [Mh, h_expand_f d ν, h_expand_f d μ, Matrix.mul_apply]
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ _
  apply Finset.sum_congr rfl
  intro l _
  rw [gramF, M_symm d κ μ]
  ring

/-- [EK] p. 24: `M⁻¹M′M⁻¹` is the matrix of the bilinear form in the f-basis. -/
theorem gram_f_eq (d : ℕ) : gramF d = (M d)⁻¹ * Mh d * (M d)⁻¹ := by
  have hu := M_det_unit d
  rw [Mh_eq_M_gramF_M, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
    Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

/-! ## (5.2): one statement for the degree of the Gram determinant -/

theorem choose_two_succ' (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

theorem choose_two_superadd (a b : ℕ) : a.choose 2 + b.choose 2 ≤ (a + b).choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, choose_two_succ', choose_two_succ']
    omega

theorem list_choose_two_le (l : List ℕ) : (l.map (fun a => a.choose 2)).sum ≤ l.sum.choose 2 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (Nat.add_le_add_left ih _).trans (choose_two_superadd a t.sum)

/-- The two formalizations of `D` in (5.1) agree. -/
theorem degD_cast (n : ℕ) : ((EKGeneralQ.degD n : ℕ) : ℤ) = EKRest.degD n := by
  unfold EKGeneralQ.degD EKRest.degD
  push_cast
  apply Finset.sum_congr rfl
  intro α _
  have hle : (α.blocks.map (fun a => a.choose 2)).sum ≤ n.choose 2 := by
    have := list_choose_two_le α.blocks
    rwa [α.blocks_sum] at this
  rw [Nat.cast_sub hle, Nat.cast_list_sum, List.map_map]
  rfl

/-- [EK] (5.1)–(5.2): the Gram determinant of the form (2.1) on `Λ′_n` over `ℤ[q]` has degree
exactly `2^{n−2}(n² − 3n + 4) − 1`, for every `n ≥ 2`. -/
theorem gram_det_natDegree_closed (n : ℕ) (hn : 2 ≤ n) :
    (((EKGeneralQ.gram (Polynomial.X : Polynomial ℤ) n).det.natDegree : ℕ) : ℤ) =
      2 ^ (n - 2) * ((n : ℤ) ^ 2 - 3 * n + 4) - 1 := by
  rw [EKGeneralQ.gram_det_natDegree, degD_cast, EKRest.eq_5_2 n hn]

/-- The same statement in `ℕ`. -/
theorem gram_det_natDegree_closed_nat (n : ℕ) (hn : 2 ≤ n) :
    (EKGeneralQ.gram (Polynomial.X : Polynomial ℤ) n).det.natDegree =
      2 ^ (n - 2) * (n ^ 2 + 4 - 3 * n) - 1 := by
  have h := gram_det_natDegree_closed n hn
  have h3 : 3 * n ≤ n ^ 2 + 4 := by nlinarith
  have hp : 1 ≤ 2 ^ (n - 2) * (n ^ 2 + 4 - 3 * n) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (Nat.sub_ne_zero_of_lt (by nlinarith)))
  zify [h3, hp]
  rw [h]
  ring

/-! ## p. 25, `n = 7`: the f-expansion of `m₇` -/

open EKRest in
/-- `(e_ν, m₇)` on the fifteen partitions of `7` (lexicographic order `EKRest.pl7`). -/
def m7fCoeff : Fin 15 → ℤ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 8, 0, 5]

open EKRest in
theorem m7_f_coord_fast : ∀ j : Fin 15,
    ∑ l, m7coeff l * fastEH (pl7 j) (pl7 l) = m7fCoeff j := by
  decide +kernel

open EKRest in
theorem pairing_e_m7 (j : Fin 15) :
    quotientPairing (ePartition (hshapes7 j).val) (EKPrimitives.mRow 7 : Q) = m7fCoeff j := by
  rw [← m7_f_coord_fast j]
  change quotientPairing _ ((mBasis 7 (EKPrimitives.rowShape 7) : degreePiece 7) : Q) = _
  rw [mBasis_val hshapes7 pl7 hs7 _ m7coeff m_seven, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_zsmul, smul_eq_mul, ← hPartition_eq_hP hshapes7 pl7 hs7 l]
  change m7coeff l * M 7 (hshapes7 j) (hshapes7 l) = _
  rw [M_fast, hs7, hs7]

open EKRest in
/-- [EK] p. 25, `n = 7`: `m₇ = 4 f₍₄,₃₎ + 8 f₍₅,₂₎ + 5 f₍₇₎` in the forgotten basis. -/
theorem m_seven_f_expansion :
    EKPrimitives.mRow 7 = (4 : ℤ) • fBasis 7 (hshapes7 10) + (8 : ℤ) • fBasis 7 (hshapes7 12) +
      (5 : ℤ) • fBasis 7 (hshapes7 14) := by
  apply (fBasis 7).repr.injective
  ext ν
  obtain ⟨j, rfl⟩ := exhaust7 ν
  rw [f_coordinates, pairing_e_m7]
  simp only [map_add, map_zsmul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  have e : ∀ i : Fin 15, (hshapes7 i = hshapes7 j) ↔ i = j := fun i => inj7.eq_iff
  simp only [e]
  fin_cases j <;> decide

open EKRest in
/-- `f₇` and `m₇` are linearly independent over `ℤ`: `a f₇ = b m₇` forces `a = b = 0`. In
particular `f₇` is not a rational (let alone integer or sign) multiple of `m₇`. -/
theorem f_seven_m_seven_independent (a b : ℤ) :
    a • fBasis 7 (EKPrimitives.rowShape 7) = b • EKPrimitives.mRow 7 → a = 0 ∧ b = 0 := by
  intro h
  rw [rowShape_seven, m_seven_f_expansion] at h
  have hc := fun i => congrArg (fun x => (fBasis 7).repr x (hshapes7 i)) h
  have h10 := hc 10
  have h14 := hc 14
  simp only [map_add, map_zsmul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, smul_add, inj7.eq_iff] at h10 h14
  norm_num at h10 h14
  omega

end OddMath.Frontier.EKMore
