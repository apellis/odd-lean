import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Littlewood–Richardson triangles and Knutson–Tao hives

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §4.3, pp. 15–19,
following Pak–Vallejo.

* `V R n = R^{Idx n}`, coordinates `a_{i,j}`, `0 ≤ i ≤ j ≤ n`; `Fintype.card (Idx n) = C(n+2,2)`
  (`card_idx`). `coord A i j` extends `A` by `0` outside `0 ≤ i ≤ j ≤ n` (E, p. 18, "as a matter
  of convention").
* Definition 4.11 (p. 16): `IsLRTriangle`, with condition (3) for `1 ≤ i ≤ j < n`.
  The printed range `1 ≤ i < j < n` is `IsLRTrianglePrinted`. The normalization `a_{0,0} = 0`
  is part of `IsLRTriangle`: the hive side has `h_{0,0} = 0` and `h_{0,0} = a_{0,0}`.
* Definition 4.14, (4.15) (p. 18): `IsHive`, conditions (R), (V), (L).
* Theorem 4.15 (p. 18): `phi` (4.16) is a linear isomorphism of determinant `1`
  (`det_phi`, `phiEquiv`), measure preserving on `V ℝ n` (`phi_measurePreserving`), with
  `IsHive (phi A) ↔ IsLRTriangle A` (`isHive_phi_iff`) and matching `λ, μ, ν`
  (`lamH_phi`, `muH_phi`, `nuH_phi`); hence `phi` maps `△_LR(λ,μ,ν)` bijectively onto
  `𝔥(λ,μ,ν)` (`phi_bijOn`).
* (4.16) (p. 18): `coord_phi_eq`; (4.17) (p. 18): `phi_rec_zero`, `phi_rec_top`, `phi_rec`,
  `phi_rec_diag`.
* (4.12), (4.13), (4.18) (pp. 17, 19): `Y`, `Qtri`, `QH`, and `QH (phi A) = Qtri A` (`QH_phi`),
  i.e. `Q_𝔥 = Q_△ ∘ Φ⁻¹` on `h_{0,0} = 0` (`QH_eq`).
* Erratum to Definition 4.11 (3): the triangle `A = (0; 2, 0; 0, 1, 1)` (`n = 2`) is the unique
  point of the printed `△_LR((2,2),(2),(1,1))` (`printed_points`), but `phi A` violates (L)
  (`printed_not_hive`), so the printed Theorem 4.15 fails; the corrected
  `△_LR((2,2),(2),(1,1))` is empty (`corrected_empty`).
* Examples 4.13 and 4.16 (pp. 17, 19): `example_4_13`, `example_4_16`.
-/

namespace OddMath.Frontier.OddLRHive

open scoped BigOperators
open Finset

/-! ## The space `V` -/

/-- Coordinate positions `(i, j)`, `0 ≤ i ≤ j ≤ n`. -/
def Idx (n : ℕ) : Type := {p : Fin (n+1) × Fin (n+1) // p.1 ≤ p.2}

variable {n : ℕ}

instance : Fintype (Idx n) := by unfold Idx; infer_instance
instance : DecidableEq (Idx n) := by unfold Idx; infer_instance

namespace Idx

/-- Row index `i`. -/
def i (x : Idx n) : ℕ := x.1.1.val
/-- Column index `j`. -/
def j (x : Idx n) : ℕ := x.1.2.val

theorem i_le_j (x : Idx n) : x.i ≤ x.j := x.2
theorem j_le (x : Idx n) : x.j ≤ n := Nat.lt_succ_iff.mp x.1.2.isLt

/-- The position `(i, j)`. -/
def mk (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) : Idx n :=
  ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), by simpa [Fin.le_def] using hij⟩

@[simp] theorem mk_i (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) : (mk i j hij hj : Idx n).i = i := rfl
@[simp] theorem mk_j (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) : (mk i j hij hj : Idx n).j = j := rfl

theorem ext {x y : Idx n} (hi : x.i = y.i) (hj : x.j = y.j) : x = y :=
  Subtype.ext (Prod.ext (Fin.ext hi) (Fin.ext hj))

@[simp] theorem mk_self (x : Idx n) : mk x.i x.j x.i_le_j x.j_le = x := ext rfl rfl

/-- Order key: column first, then row. -/
def key (x : Idx n) : Lex (ℕ × ℕ) := toLex (x.j, x.i)

theorem key_injective : Function.Injective (key : Idx n → Lex (ℕ × ℕ)) := by
  intro x y h
  have h' := congrArg ofLex h
  simp only [key, ofLex_toLex, Prod.mk.injEq] at h'
  exact ext h'.2 h'.1

instance : LinearOrder (Idx n) := LinearOrder.lift' key key_injective

theorem le_iff (x y : Idx n) : x ≤ y ↔ key x ≤ key y := Iff.rfl

theorem le_of_le_le {x y : Idx n} (hi : x.i ≤ y.i) (hj : x.j ≤ y.j) : x ≤ y := by
  rw [le_iff, key, key, Prod.Lex.le_iff]
  rcases Nat.lt_or_ge x.j y.j with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by simp; omega, hi⟩

/-- `Idx n ≃ Σ j ≤ n, {i ≤ j}`. -/
def sigmaEquiv (n : ℕ) : Idx n ≃ Σ j : Fin (n+1), Fin (j.val + 1) where
  toFun x := ⟨x.1.2, ⟨x.i, Nat.lt_succ_of_le x.i_le_j⟩⟩
  invFun y := mk y.2.val y.1.val (Nat.lt_succ_iff.mp y.2.isLt) (Nat.lt_succ_iff.mp y.1.isLt)
  left_inv x := ext rfl rfl
  right_inv y := by
    obtain ⟨a, b⟩ := y
    rfl

end Idx

theorem sum_idx {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ → M) :
    ∑ x : Idx n, g x.i x.j = ∑ j ∈ range (n+1), ∑ i ∈ range (j+1), g i j := by
  rw [← (Idx.sigmaEquiv n).symm.sum_comp, Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ range (j+1), g i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun i => g i j) (j.val + 1)

/-- E §4.3, p. 16: `V_ℤ = ℤ^{C(n+2, 2)}`. -/
theorem card_idx (n : ℕ) : Fintype.card (Idx n) = (n+2).choose 2 := by
  have h := sum_idx (n := n) (fun _ _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Finset.card_range] at h
  rw [h, Nat.choose_two_right, ← Finset.sum_range_id, Finset.sum_range_succ' (fun i => i) (n+1)]
  simp

/-- The ambient space `V_R = R^{C(n+2,2)}` of triangles and hives (E §4.3, p. 16). -/
abbrev V (R : Type*) (n : ℕ) := Idx n → R

variable {R : Type*}

/-- `a_{i,j}`, with `a_{i,j} = 0` unless `0 ≤ i ≤ j ≤ n` (E p. 18). -/
def coord [Zero R] (A : V R n) (i j : ℕ) : R :=
  if h : i ≤ j ∧ j ≤ n then A (Idx.mk i j h.1 h.2) else 0

section coord
variable [Zero R]

theorem coord_idx (A : V R n) (x : Idx n) : coord A x.i x.j = A x := by
  rw [coord, dif_pos ⟨x.i_le_j, x.j_le⟩, Idx.mk_self]

theorem coord_of_lt (A : V R n) {i j : ℕ} (h : j < i) : coord A i j = 0 := by
  rw [coord, dif_neg (by omega)]

theorem coord_of_gt (A : V R n) {i j : ℕ} (h : n < j) : coord A i j = 0 := by
  rw [coord, dif_neg (by omega)]

theorem coord_mk (A : V R n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    coord A i j = A (Idx.mk i j hij hj) := by
  rw [coord, dif_pos ⟨hij, hj⟩]

theorem ext_coord {A B : V R n} (h : ∀ i j, i ≤ j → j ≤ n → coord A i j = coord B i j) :
    A = B := by
  funext x
  rw [← coord_idx A x, ← coord_idx B x]
  exact h _ _ x.i_le_j x.j_le

end coord

/-! ## The map `Φ` (4.16) -/

section phi
variable [CommRing R]

/-- The matrix of `Φ`: `h_{i,j} = Σ_{p ≤ i, q ≤ j} a_{p,q}`. -/
def phiMatrix (R : Type*) [CommRing R] (n : ℕ) : Matrix (Idx n) (Idx n) R :=
  fun x y => if y.i ≤ x.i ∧ y.j ≤ x.j then 1 else 0

/-- E Theorem 4.15, (4.16), p. 18: `Φ : V → V`, `h_{i,j} = Σ_{p=0}^{i} Σ_{q=p}^{j} a_{p,q}`. -/
def phi (R : Type*) [CommRing R] (n : ℕ) : V R n →ₗ[R] V R n := Matrix.toLin' (phiMatrix R n)

theorem phi_apply (A : V R n) (x : Idx n) :
    phi R n A x = ∑ y : Idx n, if y.i ≤ x.i ∧ y.j ≤ x.j then A y else 0 := by
  simp only [phi, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, phiMatrix, ite_mul, one_mul,
    zero_mul]

/-- Rectangle sums `Σ_{p ≤ i} Σ_{q ≤ j} a_{p,q}`. -/
def rect (A : V R n) (i j : ℕ) : R := ∑ p ∈ range (i+1), ∑ q ∈ range (j+1), coord A p q

theorem sum_row_range (A : V R n) (p j : ℕ) {m : ℕ} (hm : j < m) :
    ∑ q ∈ range m, (if q ≤ j then coord A p q else 0) = ∑ q ∈ range (j+1), coord A p q := by
  rw [← Finset.sum_filter]
  congr 1
  ext q
  simp only [mem_filter, mem_range]
  omega

/-- E (4.16): `h_{i,j} = Σ_{p=0}^{i} Σ_{q=p}^{j} a_{p,q}` as a rectangle sum. -/
theorem coord_phi (A : V R n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    coord (phi R n A) i j = rect A i j := by
  rw [coord_mk _ hij hj, phi_apply]
  have hg : ∀ y : Idx n, (if y.i ≤ (Idx.mk i j hij hj : Idx n).i ∧
      y.j ≤ (Idx.mk i j hij hj : Idx n).j then A y else 0) =
      (fun p q => if p ≤ i ∧ q ≤ j then coord A p q else 0) y.i y.j := by
    intro y
    simp only [Idx.mk_i, Idx.mk_j, coord_idx]
  rw [Finset.sum_congr rfl (fun y _ => hg y)]
  refine (sum_idx (n := n) (fun p q => if p ≤ i ∧ q ≤ j then coord A p q else 0)).trans ?_
  -- both sides equal `Σ_{q ≤ n} Σ_{p ≤ n} [p ≤ i][q ≤ j] a_{p,q}`
  have hl : ∀ q ∈ range (n+1), ∑ p ∈ range (q+1), (if p ≤ i ∧ q ≤ j then coord A p q else 0) =
      ∑ p ∈ range (n+1), (if p ≤ i ∧ q ≤ j then coord A p q else 0) := by
    intro q hq
    rw [mem_range] at hq
    apply Finset.sum_subset
    · intro p hp
      simp only [mem_range] at hp ⊢
      omega
    · intro p _ hp
      simp only [mem_range] at hp
      rw [coord_of_lt A (by omega), ite_self]
  rw [Finset.sum_congr rfl hl, Finset.sum_comm, rect]
  have hr : ∀ p ∈ range (n+1), ∑ q ∈ range (n+1), (if p ≤ i ∧ q ≤ j then coord A p q else 0) =
      if p ≤ i then ∑ q ∈ range (j+1), coord A p q else 0 := by
    intro p _
    split_ifs with hp
    · simp only [hp, true_and]
      exact sum_row_range A p j (by omega)
    · simp [hp]
  rw [Finset.sum_congr rfl hr, ← Finset.sum_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_range]
  omega

theorem rect_succ_left (A : V R n) (i j : ℕ) :
    rect A (i+1) j = rect A i j + ∑ q ∈ range (j+1), coord A (i+1) q := by
  rw [rect, Finset.sum_range_succ, ← rect]

theorem rect_succ_right (A : V R n) (i j : ℕ) :
    rect A i (j+1) = rect A i j + ∑ p ∈ range (i+1), coord A p (j+1) := by
  simp only [rect, Finset.sum_range_succ, Finset.sum_add_distrib]

theorem sum_range_eq_Icc (A : V R n) (i j : ℕ) :
    ∑ q ∈ range (j+1), coord A i q = ∑ q ∈ Icc i j, coord A i q := by
  apply (Finset.sum_subset _ _).symm
  · intro q hq
    simp only [mem_Icc, mem_range] at hq ⊢
    omega
  · intro q hq hq'
    simp only [mem_Icc, mem_range] at hq hq'
    exact coord_of_lt A (by omega)

/-- E (4.16), p. 18, literally: `h_{i,j} = Σ_{p=0}^{i} Σ_{q=p}^{j} a_{p,q}`. -/
theorem coord_phi_eq (A : V R n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    coord (phi R n A) i j = ∑ p ∈ range (i+1), ∑ q ∈ Icc p j, coord A p q := by
  rw [coord_phi A hij hj, rect]
  exact Finset.sum_congr rfl fun p _ => sum_range_eq_Icc A p j

theorem sum_range_diag (A : V R n) (i : ℕ) :
    ∑ q ∈ range (i+1), coord A (i+1) q = 0 :=
  Finset.sum_eq_zero fun q hq => coord_of_lt A (by simp at hq; omega)

/-! ### Differences of `Φ(A)` -/

theorem phi_zero_zero (A : V R n) : coord (phi R n A) 0 0 = coord A 0 0 := by
  rw [coord_phi A le_rfl (Nat.zero_le _), rect]
  simp

/-- Vertical differences: `h_{i,j+1} - h_{i,j} = Σ_{p ≤ i} a_{p,j+1}`. -/
theorem phi_col (A : V R n) {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    coord (phi R n A) i (j+1) - coord (phi R n A) i j = ∑ p ∈ range (i+1), coord A p (j+1) := by
  rw [coord_phi A (by omega) hj, coord_phi A hij hj.le, rect_succ_right, add_sub_cancel_left]

/-- Row differences: `h_{i+1,j} - h_{i,j} = Σ_{q=i+1}^{j} a_{i+1,q}`. -/
theorem phi_row (A : V R n) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    coord (phi R n A) (i+1) j - coord (phi R n A) i j = ∑ q ∈ Icc (i+1) j, coord A (i+1) q := by
  rw [coord_phi A hij hj, coord_phi A hij.le hj, rect_succ_left, add_sub_cancel_left,
    sum_range_eq_Icc]

/-- `(R)`-differences: `(h_{i+1,j+1} - h_{i+1,j}) - (h_{i,j+1} - h_{i,j}) = a_{i+1,j+1}`. -/
theorem phi_rhombus (A : V R n) {i j : ℕ} (hij : i < j) (hj : j < n) :
    (coord (phi R n A) (i+1) (j+1) - coord (phi R n A) (i+1) j) -
      (coord (phi R n A) i (j+1) - coord (phi R n A) i j) = coord A (i+1) (j+1) := by
  rw [phi_col A (by omega) hj, phi_col A hij.le hj, Finset.sum_range_succ, add_sub_cancel_left]

/-- Diagonal differences: `h_{j,j} - h_{j-1,j-1} = Σ_{p ≤ j} a_{p,j}`. -/
theorem phi_diag (A : V R n) {j : ℕ} (hj : j < n) :
    coord (phi R n A) (j+1) (j+1) - coord (phi R n A) j j = ∑ p ∈ range (j+2), coord A p (j+1) := by
  rw [coord_phi A le_rfl (by omega), coord_phi A le_rfl hj.le, rect_succ_left, rect_succ_right,
    Finset.sum_range_succ (fun q => coord A (j+1) q), sum_range_diag, zero_add,
    Finset.sum_range_succ (fun p => coord A p (j+1)) (j+1)]
  abel

/-! ### (4.17) -/

/-- E (4.17), `i = j = 0`: `h_{0,0} = a_{0,0}`. -/
theorem phi_rec_zero (A : V R n) : coord (phi R n A) 0 0 = coord A 0 0 := phi_zero_zero A

/-- E (4.17), `i = 0 < j`: `h_{0,j} = a_{0,j} + h_{0,j-1}` (`h_{-1,·} = 0`). -/
theorem phi_rec_top (A : V R n) {j : ℕ} (hj : j < n) :
    coord (phi R n A) 0 (j+1) = coord A 0 (j+1) + coord (phi R n A) 0 j := by
  have := phi_col A (Nat.zero_le j) hj
  rw [Finset.sum_range_one] at this
  rw [← this]
  abel

/-- E (4.17), `0 < i < j`: `h_{i,j} = a_{i,j} + h_{i-1,j} + h_{i,j-1} - h_{i-1,j-1}`. -/
theorem phi_rec (A : V R n) {i j : ℕ} (hij : i < j) (hj : j < n) :
    coord (phi R n A) (i+1) (j+1) = coord A (i+1) (j+1) + coord (phi R n A) i (j+1) +
      coord (phi R n A) (i+1) j - coord (phi R n A) i j := by
  rw [← phi_rhombus A hij hj]
  abel

/-- E (4.17), `0 < i = j`: `h_{i,i} = a_{i,i} + h_{i-1,i}`. -/
theorem phi_rec_diag (A : V R n) {i : ℕ} (hi : i < n) :
    coord (phi R n A) (i+1) (i+1) = coord A (i+1) (i+1) + coord (phi R n A) i (i+1) := by
  have := phi_row A (Nat.lt_succ_self i) (by omega)
  rw [Finset.Icc_self, Finset.sum_singleton] at this
  rw [← this]
  abel

/-! ### Determinant and inverse -/

theorem phiMatrix_lower : (phiMatrix R n).BlockTriangular OrderDual.toDual := by
  intro x y hxy
  have hxy' : x < y := hxy
  simp only [phiMatrix]
  rw [if_neg]
  rintro ⟨hi, hj⟩
  exact absurd (Idx.le_of_le_le hi hj) (not_le.mpr hxy')

theorem det_phiMatrix : (phiMatrix R n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ phiMatrix_lower]
  simp [phiMatrix]

/-- E Theorem 4.15, p. 18: `Φ` has determinant `1`. -/
theorem det_phi : LinearMap.det (phi R n) = 1 := by
  rw [phi, LinearMap.det_toLin', det_phiMatrix]

/-- E Theorem 4.15, p. 18: `Φ` is an isomorphism (over any commutative ring, e.g. `V_ℤ`). -/
noncomputable def phiEquiv (R : Type*) [CommRing R] (n : ℕ) : V R n ≃ₗ[R] V R n :=
  letI : Invertible (phiMatrix R n).det := invertibleOne.copy _ det_phiMatrix
  Matrix.toLinearEquiv' (phiMatrix R n) (Matrix.invertibleOfDetInvertible _)

@[simp] theorem phiEquiv_apply (A : V R n) : phiEquiv R n A = phi R n A := rfl

end phi

/-- E Theorem 4.15, p. 18: `Φ` is volume preserving on `V = V_ℤ ⊗ ℝ`. -/
theorem phi_measurePreserving :
    MeasureTheory.MeasurePreserving (phi ℝ n) MeasureTheory.volume MeasureTheory.volume := by
  refine ⟨(phi ℝ n).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [det_phi]; exact one_ne_zero),
    det_phi]
  simp

/-! ## Littlewood–Richardson triangles and hives -/

section cones
variable [CommRing R] [PartialOrder R]

/-- E Definition 4.11, p. 16, with condition (3) for `1 ≤ i ≤ j < n` and `a_{0,0} = 0`. -/
structure IsLRTriangle (A : V R n) : Prop where
  zero : coord A 0 0 = 0
  nonneg : ∀ i j, 1 ≤ i → i < j → j ≤ n → 0 ≤ coord A i j
  column : ∀ i j, 1 ≤ i → i ≤ j → j < n →
    ∑ p ∈ range (i+1), coord A p (j+1) ≤ ∑ p ∈ range i, coord A p j
  lattice : ∀ i j, 1 ≤ i → i ≤ j → j < n →
    ∑ q ∈ Icc (i+1) (j+1), coord A (i+1) q ≤ ∑ q ∈ Icc i j, coord A i q

/-- E Definition 4.11, p. 16, as printed: condition (3) only for `1 ≤ i < j < n`. -/
structure IsLRTrianglePrinted (A : V R n) : Prop where
  nonneg : ∀ i j, 1 ≤ i → i < j → j ≤ n → 0 ≤ coord A i j
  column : ∀ i j, 1 ≤ i → i ≤ j → j < n →
    ∑ p ∈ range (i+1), coord A p (j+1) ≤ ∑ p ∈ range i, coord A p j
  lattice : ∀ i j, 1 ≤ i → i < j → j < n →
    ∑ q ∈ Icc (i+1) (j+1), coord A (i+1) q ≤ ∑ q ∈ Icc i j, coord A i q

theorem IsLRTriangle.printed {A : V R n} (hA : IsLRTriangle A) : IsLRTrianglePrinted A :=
  ⟨hA.nonneg, hA.column, fun i j hi hij hj => hA.lattice i j hi hij.le hj⟩

/-- `λ_j = Σ_{p=0}^{j} a_{p,j}` (E p. 16). -/
def lamT (A : V R n) (j : ℕ) : R := ∑ p ∈ range (j+1), coord A p j
/-- `μ_j = a_{0,j}` (E p. 16). -/
def muT (A : V R n) (j : ℕ) : R := coord A 0 j
/-- `ν_i = Σ_{q=i}^{n} a_{i,q}` (E p. 16; the printed upper limit `k` reads `n`). -/
def nuT (A : V R n) (i : ℕ) : R := ∑ q ∈ Icc i n, coord A i q

/-- `△_LR(λ, μ, ν)`; `λ, μ, ν` are compared in positions `1, …, n`. -/
def triangles (n : ℕ) (lam mu nu : ℕ → R) : Set (V R n) :=
  {A | IsLRTriangle A ∧ ∀ j, 1 ≤ j → j ≤ n → lamT A j = lam j ∧ muT A j = mu j ∧ nuT A j = nu j}

/-- The printed `△_LR(λ, μ, ν)`. -/
def trianglesPrinted (n : ℕ) (lam mu nu : ℕ → R) : Set (V R n) :=
  {A | IsLRTrianglePrinted A ∧
    ∀ j, 1 ≤ j → j ≤ n → lamT A j = lam j ∧ muT A j = mu j ∧ nuT A j = nu j}

/-- E Definition 4.14, (4.15), p. 18: hives. -/
structure IsHive (H : V R n) : Prop where
  zero : coord H 0 0 = 0
  R : ∀ i j, 1 ≤ i → i < j → j ≤ n →
    coord H (i-1) j - coord H (i-1) (j-1) ≤ coord H i j - coord H i (j-1)
  V : ∀ i j, 1 ≤ i → i ≤ j → j < n →
    coord H i (j+1) - coord H i j ≤ coord H (i-1) j - coord H (i-1) (j-1)
  L : ∀ i j, 1 ≤ i → i ≤ j → j < n →
    coord H (i+1) (j+1) - coord H i (j+1) ≤ coord H i j - coord H (i-1) j

/-- `λ_j = h_{j,j} - h_{j-1,j-1}` (E p. 18). -/
def lamH (H : V R n) (j : ℕ) : R := coord H j j - coord H (j-1) (j-1)
/-- `μ_j = h_{0,j} - h_{0,j-1}` (E p. 18). -/
def muH (H : V R n) (j : ℕ) : R := coord H 0 j - coord H 0 (j-1)
/-- `ν_i = h_{i,n} - h_{i-1,n}` (E p. 18). -/
def nuH (H : V R n) (i : ℕ) : R := coord H i n - coord H (i-1) n

/-- `𝔥(λ, μ, ν)`. -/
def hives (n : ℕ) (lam mu nu : ℕ → R) : Set (V R n) :=
  {H | IsHive H ∧ ∀ j, 1 ≤ j → j ≤ n → lamH H j = lam j ∧ muH H j = mu j ∧ nuH H j = nu j}

omit [PartialOrder R] in
theorem lamH_phi (A : V R n) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ n) :
    lamH (phi R n A) j = lamT A j := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [lamH, Nat.add_sub_cancel, phi_diag A (by omega), lamT]

omit [PartialOrder R] in
theorem muH_phi (A : V R n) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ n) :
    muH (phi R n A) j = muT A j := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [muH, Nat.add_sub_cancel, phi_col A (Nat.zero_le j) (by omega), Finset.sum_range_one, muT]

omit [PartialOrder R] in
theorem nuH_phi (A : V R n) {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ n) :
    nuH (phi R n A) i = nuT A i := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [nuH, Nat.add_sub_cancel, phi_row A (by omega) le_rfl, nuT]

variable [IsOrderedRing R]

/-- E Theorem 4.15, p. 18, cone part (with the corrected Definition 4.11 (3)):
`(R) ↔ (1)`, `(V) ↔ (2)`, `(L) ↔ (3)`. -/
theorem isHive_phi_iff (A : V R n) : IsHive (phi R n A) ↔ IsLRTriangle A := by
  constructor
  · intro hH
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← phi_zero_zero]; exact hH.zero
    · intro i j hi hij hj
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have := hH.R (i+1) (j+1) hi hij hj
      simp only [Nat.add_sub_cancel] at this
      rw [← phi_rhombus A (by omega) (by omega)]
      exact sub_nonneg.mpr this
    · intro i j hi hij hj
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have := hH.V (i+1) (j+1) hi hij hj
      simp only [Nat.add_sub_cancel] at this
      rwa [phi_col A hij hj, phi_col A (by omega) (by omega)] at this
    · intro i j hi hij hj
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have := hH.L (i+1) j hi hij hj
      simp only [Nat.add_sub_cancel] at this
      rwa [phi_row A (by omega) (by omega), phi_row A (by omega) (by omega)] at this
  · intro hA
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [phi_zero_zero]; exact hA.zero
    · intro i j hi hij hj
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have := hA.nonneg (i+1) (j+1) hi hij hj
      rw [← phi_rhombus A (by omega) (by omega)] at this
      exact sub_nonneg.mp this
    · intro i j hi hij hj
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [phi_col A hij hj, phi_col A (by omega) (by omega)]
      exact hA.column (i+1) (j+1) hi hij hj
    · intro i j hi hij hj
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [phi_row A (by omega) (by omega), phi_row A (by omega) (by omega)]
      exact hA.lattice (i+1) j hi hij hj

/-- E Theorem 4.15, p. 18 (corrected Definition 4.11 (3)): `Φ` maps `△_LR(λ, μ, ν)` bijectively
onto `𝔥(λ, μ, ν)`, for all `λ, μ, ν`. -/
theorem phi_bijOn (lam mu nu : ℕ → R) :
    Set.BijOn (phi R n) (triangles n lam mu nu) (hives n lam mu nu) := by
  refine ⟨?_, (phiEquiv R n).injective.injOn, ?_⟩
  · rintro A ⟨hA, hp⟩
    refine ⟨(isHive_phi_iff A).mpr hA, fun j h1 hj => ?_⟩
    rw [lamH_phi A h1 hj, muH_phi A h1 hj, nuH_phi A h1 hj]
    exact hp j h1 hj
  · rintro H ⟨hH, hp⟩
    refine ⟨(phiEquiv R n).symm H, ⟨?_, fun j h1 hj => ?_⟩, (phiEquiv R n).apply_symm_apply H⟩
    · rw [← isHive_phi_iff, ← phiEquiv_apply, LinearEquiv.apply_symm_apply]; exact hH
    · rw [← lamH_phi _ h1 hj, ← muH_phi _ h1 hj, ← nuH_phi _ h1 hj, ← phiEquiv_apply,
        LinearEquiv.apply_symm_apply]
      exact hp j h1 hj

end cones

/-! ## The quadratic forms (4.12), (4.13), (4.18) -/

section forms
variable [CommRing R]

theorem sum_Icc_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Icc 1 m, f i = ∑ i ∈ range m, f (i+1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 m 1]
  congr 1

/-- E (4.12), p. 17: `Y_{i,j} = Σ_{p=0}^{i-1} Σ_{q=p}^{j-1} a_{p,q}`. -/
def Y (A : V R n) (i j : ℕ) : R := ∑ p ∈ range i, ∑ q ∈ Ico p j, coord A p q

/-- E (4.13), p. 17: `Q_△(A) = Σ_{i=0}^{n} Σ_{j=i}^{n} a_{i,j} Y_{i,j}`. -/
def Qtri (A : V R n) : R := ∑ i ∈ range (n+1), ∑ j ∈ Icc i n, coord A i j * Y A i j

/-- E (4.18), p. 19: `Q_𝔥(H) = Σ_{i=1}^{n} Σ_{j=i}^{n} h_{i-1,j-1} (h_{i,j} - h_{i-1,j} - h_{i,j-1} +
h_{i-1,j-1}) - Σ_{i=1}^{n-1} h_{i,i}²`. -/
def QH (H : V R n) : R :=
  (∑ i ∈ Icc 1 n, ∑ j ∈ Icc i n, coord H (i-1) (j-1) *
      (coord H i j - coord H (i-1) j - coord H i (j-1) + coord H (i-1) (j-1))) -
    ∑ i ∈ Icc 1 (n-1), coord H i i ^ 2

theorem Y_eq_rect (A : V R n) (i j : ℕ) :
    Y A (i+1) (j+1) = rect A i j := by
  rw [Y, rect]
  refine Finset.sum_congr rfl fun p hp => ?_
  apply Finset.sum_subset
  · intro q hq
    simp only [mem_Ico, mem_range] at hq ⊢
    omega
  · intro q hq hq'
    simp only [mem_Ico, mem_range] at hq hq'
    exact coord_of_lt A (by omega)

theorem Qtri_eq (A : V R n) :
    Qtri A = ∑ i ∈ range n, ∑ j ∈ Icc (i+1) n, coord A (i+1) j * rect A i (j-1) := by
  rw [Qtri, Finset.sum_range_succ']
  simp only [Y, Finset.range_zero, Finset.sum_empty, mul_zero, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by simp at hj; omega⟩
  rw [← Y, Nat.add_sub_cancel, Y_eq_rect A i j]

/-- E (4.18), p. 19: `Q_𝔥(Φ A) = Q_△(A)` whenever `a_{0,0} = 0`. -/
theorem QH_phi (A : V R n) (h0 : coord A 0 0 = 0) : QH (phi R n A) = Qtri A := by
  set H := phi R n A with hH
  have hterm : ∀ i ∈ range n, ∀ j ∈ Icc (i+1) n,
      coord H i (j-1) * (coord H (i+1) j - coord H i j - coord H (i+1) (j-1) + coord H i (j-1)) =
        coord A (i+1) j * rect A i (j-1) + (if j = i+1 then coord H i i ^ 2 else 0) := by
    intro i hi j hj
    simp only [mem_range, mem_Icc] at hi hj
    rcases Nat.eq_or_lt_of_le hj.1 with rfl | hlt
    · simp only [if_true, Nat.add_sub_cancel]
      rw [coord_of_lt H (Nat.lt_succ_self i), phi_rec_diag A hi, coord_phi A le_rfl (by omega)]
      ring
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [if_neg (by omega), Nat.add_sub_cancel, add_zero]
      have hD : coord H (i+1) (j+1) - coord H i (j+1) - coord H (i+1) j + coord H i j =
          coord A (i+1) (j+1) := by
        rw [← phi_rhombus A (i := i) (j := j) (by omega) (by omega)]
        ring
      rw [hD, coord_phi A (by omega : i ≤ j) (by omega)]
      ring
  rw [QH, sum_Icc_one, Qtri_eq]
  simp only [Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (hterm i hi))]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq']
  have hdiag : ∀ i ∈ range n, (if i + 1 ∈ Icc (i+1) n then coord H i i ^ 2 else 0) =
      coord H i i ^ 2 := by
    intro i hi
    rw [if_pos (by simp at hi ⊢; omega)]
  rw [Finset.sum_congr rfl hdiag]
  rcases n with _ | m
  · simp
  · rw [Finset.sum_range_succ' (fun x => coord H x x ^ 2), Nat.add_sub_cancel,
      sum_Icc_one (fun i => coord H i i ^ 2), hH, phi_zero_zero, h0]
    ring

/-- E p. 19: `Q_𝔥 = Q_△ ∘ Φ⁻¹` on the hyperplane `h_{0,0} = 0`. -/
theorem QH_eq (H : V R n) (h0 : coord H 0 0 = 0) : QH H = Qtri ((phiEquiv R n).symm H) := by
  conv_lhs => rw [← (phiEquiv R n).apply_symm_apply H]
  refine QH_phi _ ?_
  rw [← phi_zero_zero, ← phiEquiv_apply, LinearEquiv.apply_symm_apply]
  exact h0

end forms

/-! ## The printed Definition 4.11 (3): a counterexample (`n = 2`, `λ = (2,2)`, `μ = (2)`,
`ν = (1,1)`) -/

/-- Values of the counterexample triangle: `a_{0,1} = 2`, `a_{1,2} = a_{2,2} = 1`, else `0`. -/
def cexF : ℕ → ℕ → ℤ
  | 0, 1 => 2
  | 1, 2 => 1
  | 2, 2 => 1
  | _, _ => 0

/-- The triangle `(a_{0,0}; a_{0,1}, a_{1,1}; a_{0,2}, a_{1,2}, a_{2,2}) = (0; 2, 0; 0, 1, 1)`. -/
def cex : V ℤ 2 := fun x => cexF x.i x.j

theorem coord_cex (i j : ℕ) : coord cex i j = if i ≤ j ∧ j ≤ 2 then cexF i j else 0 := by
  unfold coord
  split_ifs <;> rfl

/-- `λ = (2, 2)`, `μ = (2)`, `ν = (1, 1)`, in positions `1, 2`. -/
def lam22 (j : ℕ) : ℤ := if j = 1 ∨ j = 2 then 2 else 0
def mu2 (j : ℕ) : ℤ := if j = 1 then 2 else 0
def nu11 (j : ℕ) : ℤ := if j = 1 ∨ j = 2 then 1 else 0

theorem cex_mem_printed : cex ∈ trianglesPrinted 2 lam22 mu2 nu11 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j hi hij hj
    obtain rfl : j = 2 := by omega
    obtain rfl : i = 1 := by omega
    simp [coord_cex, cexF]
  · intro i j hi hij hj
    obtain rfl : j = 1 := by omega
    obtain rfl : i = 1 := by omega
    simp [coord_cex, cexF, Finset.sum_range_succ]
  · intro i j hi hij hj
    omega
  · intro j h1 hj
    interval_cases j
    · refine ⟨?_, ?_, ?_⟩ <;> decide
    · refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `cex` is the only point of the printed `△_LR((2,2),(2),(1,1))` with `a_{0,0} = 0`. -/
theorem printed_points (A : V ℤ 2) (hA : A ∈ trianglesPrinted 2 lam22 mu2 nu11)
    (h0 : coord A 0 0 = 0) : A = cex := by
  obtain ⟨-, hp⟩ := hA
  obtain ⟨l1, m1, n1⟩ := hp 1 le_rfl (by norm_num)
  obtain ⟨l2, m2, n2⟩ := hp 2 (by norm_num) le_rfl
  simp [lamT, muT, nuT, lam22, mu2, nu11, Finset.sum_range_succ] at l1 m1 n1 l2 m2 n2
  apply ext_coord
  intro i j hij hj
  interval_cases j <;> interval_cases i <;> simp [coord_cex, cexF] <;> linarith

theorem cex_not_lr : ¬ IsLRTriangle cex := by
  intro h
  have := h.lattice 1 1 le_rfl le_rfl (by norm_num)
  simp [coord_cex, cexF] at this

/-- E Definition 4.11 (3) corrected: `△_LR((2,2),(2),(1,1)) = ∅` (there is no LR tableau of
shape `(2,2)/(2)` and content `(1,1)`). -/
theorem corrected_empty : triangles 2 lam22 mu2 nu11 = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  have hc := printed_points A ⟨hA.1.printed, hA.2⟩ hA.1.zero
  exact cex_not_lr (hc ▸ hA.1)

/-- E Theorem 4.15 fails for the printed Definition 4.11 (3): `Φ(cex)` violates (L) at
`i = j = 1`. -/
theorem printed_not_hive : ¬ IsHive (phi ℤ 2 cex) := by
  rw [isHive_phi_iff]
  exact cex_not_lr

/-- E Theorem 4.15 fails for the printed Definition 4.11 (3): `Φ` does not map the printed
`△_LR((2,2),(2),(1,1))` into `𝔥((2,2),(2),(1,1))`. -/
theorem printed_phi_not_subset :
    ¬ Set.MapsTo (phi ℤ 2) (trianglesPrinted 2 lam22 mu2 nu11) (hives 2 lam22 mu2 nu11) :=
  fun h => printed_not_hive (h cex_mem_printed).1

/-! ## Examples 4.13 and 4.16 -/

/-- E Example 4.13, p. 17: `A_S` for `S` of shape `(3,2,1)/(2,1)` with rows `1`, `2`, `1`. -/
def exF : ℕ → ℕ → ℤ
  | 0, 1 => 2
  | 1, 1 => 1
  | 0, 2 => 1
  | 2, 2 => 1
  | 1, 3 => 1
  | _, _ => 0

def exA : V ℤ 3 := fun x => exF x.i x.j

/-- E Example 4.16, p. 19: `Φ(A_S)`. -/
def exHF : ℕ → ℕ → ℤ
  | 0, 1 => 2
  | 1, 1 => 3
  | 0, 2 => 3
  | 1, 2 => 4
  | 2, 2 => 5
  | 0, 3 => 3
  | 1, 3 => 5
  | 2, 3 => 6
  | 3, 3 => 6
  | _, _ => 0

theorem coord_exA (i j : ℕ) : coord exA i j = if i ≤ j ∧ j ≤ 3 then exF i j else 0 := by
  unfold coord
  split_ifs <;> rfl

/-- E Example 4.13, p. 17: `Q_△(A_S) = 6`. -/
theorem example_4_13 : Qtri exA = 6 := by decide

/-- E Example 4.16, p. 19: `Φ(A_S)` is the displayed hive and `Q_𝔥(Φ(A_S)) = 6`. -/
theorem example_4_16 :
    (∀ i j, i ≤ j → j ≤ 3 → coord (phi ℤ 3 exA) i j = exHF i j) ∧ QH (phi ℤ 3 exA) = 6 := by
  refine ⟨fun i j hij hj => ?_, ?_⟩
  · rw [coord_phi exA hij hj]
    interval_cases j <;> interval_cases i <;> decide
  · rw [QH_phi exA (by decide), example_4_13]

end OddMath.Frontier.OddLRHive
