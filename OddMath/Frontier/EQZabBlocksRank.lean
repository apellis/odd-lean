import OddMath.Frontier.EQZabBlocksHom
import OddMath.Frontier.EQFixZnCells
import OddMath.Frontier.EQFixZabCells
import OddMath.Frontier.QuantumSl2Plus

/-!
# Ellis–Qi, Proposition 4.13 (3): graded ranks

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, Proposition 4.13 (3), with the quantum multinomials `[n; a]_q = [n]_q! / ([a_1]_q! ⋯ [a_r]_q!)`
in `ℤ[q, q⁻¹]`, `[n]_q = (q^n − q^{−n})/(q − q^{−1})` (`QuantumSl2Plus.qFact`, `qBinom`).

In the model of `EQZabBlocks` the generator `1_z` of `Z_a` sits in degree `0`, and the basis
element `s̃_{λ_1}(X_1) ⋯ s̃_{λ_r}(X_r)` has `q`-degree `2 deg a i`, `deg a i = Σ |λ_k|`
(`Bas_mem_grading`; the variables have `q`-degree `2`). By `prop_4_13_three`, `HOM(Z_a, Z_b)` is
free over `OΛ̃_n` on the matrix units `E_{ij}` (`matrixUnit_basis`: `b_i ↦ b'_j`, `b_{i'} ↦ 0`),
of `q`-degree `2 (deg b j − deg a i)`; its graded rank is `grankHom a b`.

* `sum_T_deg`: `Σ_i q^{2 deg a i} = q^{D_a} [n; a]_q`, `D_a = Σ_k a_k (a_1 + ⋯ + a_{k−1})` (`Dsh`),
  `[n; a]_q` = `qMulti a` (`qMulti_mul_prod_qFact`: `qMulti a · Π [a_k]_q! = [n]_q!`).
* **Corrected Proposition 4.13 (3)** (`grankHom_eq`): `grank HOM(Z_a, Z_b) = q^{D_b − D_a} [n; a]_q [n; b]_q`.
* `grankHom_eq_printed_iff`, `invert_grankHom_eq_printed_iff`: the printed `[n; a]_q [n; b]_q`
  holds (for either convention `q^{deg}` or `q^{−deg}`) iff `D_a = D_b`;
  `prop_4_13_three_printed_false`: it fails for `a = (1, 1)`, `b = (2)` (ERRATA [EQ] 21). The printed
  value is the graded rank after shifting the generator of each `Z_a` to degree `−D_a`.
-/

namespace OddMath.Frontier.EQBlocks

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open OddMath.Frontier.EQSkewDifferential (theta grading)
open OddMath.Frontier.EQZab (inclX inclY)
open OddMath.Frontier.SmallRank (OLam)
open OddMath.Frontier.QuantumSl2Plus (qBinom qFact qInt)
open LaurentPolynomial MulOpposite
open scoped BigOperators

noncomputable section

local notation "A" => LaurentPolynomial ℤ

/-- The degree `Σ_k |λ_k|` of the basis element indexed by `i` (`q`-degree `2 deg a i`). -/
def deg : (a : List ℕ) → Idx a → ℕ
  | [] => fun _ => 0
  | _ :: a => fun i => deg a i.1 + ∑ j, i.2.1 j

/-- `D_a = Σ_k a_k (a_1 + ⋯ + a_{k−1})`, the top degree. -/
def Dsh : List ℕ → ℕ
  | [] => 0
  | k :: a => Dsh a + k * blocksN a

/-- The quantum multinomial `[n; a]_q`. -/
def qMulti : List ℕ → A
  | [] => 1
  | k :: a => qMulti a * qBinom k (blocksN a)

theorem Bas_mem_grading : ∀ (a : List ℕ) (i : Idx a), Bas a i ∈ grading (blocksN a) (deg a i)
  | [], _ => EQSkewDifferential.one_mem_grading'
  | k :: a, i => by
    have h := EQSkewDifferential.mul_mem_grading'
      (EQFix.inclX_mem_grading (b := k) (Bas_mem_grading a i.1))
      (EQFix.inclY_mem_grading (a := blocksN a) (EQFix.theta_mem_grading
        (EQFix.untwisted_mem_grading k i.2.1)))
    rw [← EQSchur.twisted_eq_theta_untwisted, EQFix.totalDeg_eq_sum] at h
    show _ ∈ grading _ ((deg a i.1 + ∑ j, i.2.1 j : ℕ) : ℤ)
    push_cast at h ⊢
    exact h

/-! ## The quantum multinomials -/

theorem qMulti_mul_prod_qFact : ∀ a : List ℕ,
    qMulti a * (a.map qFact).prod = qFact (blocksN a)
  | [] => by simp [qMulti, blocksN, qFact]
  | k :: a => by
    rw [qMulti, List.map_cons, List.prod_cons, show blocksN (k :: a) = blocksN a + k from rfl,
      add_comm, ← QuantumSl2Plus.qBinom_mul_qFact k (blocksN a), ← qMulti_mul_prod_qFact a]
    ring

theorem qMulti_ne_zero (a : List ℕ) : qMulti a ≠ 0 := by
  intro h
  have := qMulti_mul_prod_qFact a
  rw [h, zero_mul] at this
  exact QuantumSl2Plus.qFact_ne_zero _ this.symm

theorem sum_box_T (k m : ℕ) :
    ∑ μ ∈ BoxPartitionCount.box k m, (T (2 * ((∑ j, μ j : ℕ) : ℤ)) : A) =
      T ((k * m : ℕ) : ℤ) * qBinom k m := by
  rw [qBinom, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← T_add]; congr 1; push_cast; ring

theorem sum_T_deg : ∀ a : List ℕ,
    ∑ i : Idx a, (T (2 * (deg a i : ℤ)) : A) = T (Dsh a) * qMulti a
  | [] => by simp [deg, Dsh, qMulti, Idx]
  | k :: a => by
    show ∑ i : Idx a × ↥(BoxPartitionCount.box k (blocksN a)),
      (T (2 * ((deg a i.1 + ∑ j, i.2.1 j : ℕ) : ℤ)) : A) = T (Dsh a + k * blocksN a : ℕ) * (qMulti a * qBinom k (blocksN a))
    rw [Fintype.sum_prod_type]
    have hs : ∀ β : Idx a, ∑ μ : ↥(BoxPartitionCount.box k (blocksN a)),
        (T (2 * ((deg a β + ∑ j, μ.1 j : ℕ) : ℤ)) : A) =
          T (2 * (deg a β : ℤ)) * (T ((k * blocksN a : ℕ) : ℤ) * qBinom k (blocksN a)) := by
      intro β
      rw [← sum_box_T, Finset.mul_sum]
      exact (Finset.sum_coe_sort (BoxPartitionCount.box k (blocksN a))
        (fun μ : Fin k → ℕ => (T (2 * ((deg a β + ∑ j, μ j : ℕ) : ℤ)) : A))).trans
        (Finset.sum_congr rfl fun μ _ => by rw [← T_add]; congr 1; push_cast; ring)
    simp only [hs]
    rw [← Finset.sum_mul, sum_T_deg a]
    rw [show (T ((Dsh a + k * blocksN a : ℕ) : ℤ) : A) = T (Dsh a) * T ((k * blocksN a : ℕ) : ℤ) by
      rw [← T_add]; push_cast; rfl]
    ring

theorem invert_qInt (n : ℕ) : invert (qInt n) = qInt n := by
  rw [qInt, map_sum]
  simp only [invert_T]
  rw [← Finset.sum_range_reflect (fun i => (T ((n : ℤ) - 1 - 2 * (i : ℤ)) : A)) n]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < n := Finset.mem_range.mp hi
  congr 1
  omega

theorem invert_qFact (n : ℕ) : invert (qFact n) = qFact n := by
  rw [qFact, map_prod]
  exact Finset.prod_congr rfl fun i _ => invert_qInt _

theorem invert_qBinom (k m : ℕ) : invert (qBinom k m) = qBinom k m := by
  have h := congrArg invert (QuantumSl2Plus.qBinom_mul_qFact k m)
  rw [map_mul, map_mul, invert_qFact, invert_qFact, invert_qFact,
    ← QuantumSl2Plus.qBinom_mul_qFact k m] at h
  exact mul_right_cancel₀ (QuantumSl2Plus.qFact_ne_zero k)
    (mul_right_cancel₀ (QuantumSl2Plus.qFact_ne_zero m) h)

theorem invert_qMulti : ∀ a : List ℕ, invert (qMulti a) = qMulti a
  | [] => map_one _
  | k :: a => by rw [qMulti, map_mul, invert_qMulti a, invert_qBinom]

theorem sum_T_neg_deg (a : List ℕ) :
    ∑ i : Idx a, (T (-(2 * (deg a i : ℤ))) : A) = T (-(Dsh a : ℤ)) * qMulti a := by
  have h := congrArg invert (sum_T_deg a)
  rw [map_sum, map_mul, invert_T, invert_qMulti] at h
  simpa only [invert_T] using h

/-! ## The graded rank of `HOM(Z_a, Z_b)` -/

/-- The graded rank `Σ_{i,j} q^{2(deg b j − deg a i)}` of `HOM(Z_a, Z_b)`, free on the
matrix units `E_{ij}`. -/
def grankHom (a b : List ℕ) : A :=
  ∑ i : Idx a, ∑ j : Idx b, T (2 * ((deg b j : ℤ) - deg a i))

/-- **Proposition 4.13 (3), corrected**: `grank HOM(Z_a, Z_b) = q^{D_b − D_a} [n; a]_q [n; b]_q`. -/
theorem grankHom_eq (a b : List ℕ) :
    grankHom a b = T ((Dsh b : ℤ) - Dsh a) * qMulti a * qMulti b := by
  have h : grankHom a b = (∑ i : Idx a, (T (-(2 * (deg a i : ℤ))) : A)) *
      ∑ j : Idx b, (T (2 * (deg b j : ℤ)) : A) := by
    rw [grankHom, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← T_add]; congr 1; ring
  rw [h, sum_T_neg_deg, sum_T_deg, sub_eq_add_neg, T_add]
  ring

theorem T_mul_eq_self_iff {x : ℤ} {c : A} (hc : c ≠ 0) : T x * c = c ↔ x = 0 := by
  constructor
  · intro h
    have h1 : (T x - 1) * c = 0 := by rw [sub_mul, h, one_mul, sub_self]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact QuantumSl2Plus.T_injective ((sub_eq_zero.mp h2).trans T_zero.symm)
    · exact absurd h2 hc
  · rintro rfl; rw [T_zero, one_mul]

/-- The printed graded rank `[n; a]_q [n; b]_q` holds iff `D_a = D_b`. -/
theorem grankHom_eq_printed_iff (a b : List ℕ) :
    grankHom a b = qMulti a * qMulti b ↔ Dsh a = Dsh b := by
  rw [grankHom_eq, mul_assoc, T_mul_eq_self_iff (mul_ne_zero (qMulti_ne_zero a) (qMulti_ne_zero b))]
  omega

/-- The same for the opposite convention `q^{−deg}`. -/
theorem invert_grankHom_eq_printed_iff (a b : List ℕ) :
    invert (grankHom a b) = qMulti a * qMulti b ↔ Dsh a = Dsh b := by
  rw [grankHom_eq, map_mul, map_mul, invert_T, invert_qMulti, invert_qMulti, mul_assoc,
    T_mul_eq_self_iff (mul_ne_zero (qMulti_ne_zero a) (qMulti_ne_zero b))]
  omega

/-- **The printed Proposition 4.13 (3) is false** with `1_z` in degree `0`: for `n = 2`,
`a = (1, 1)`, `b = (2)`, `grank HOM(Z_a, Z_b) = 1 + q^{−2} ≠ [2]_q = q + q^{−1}` (in either
convention). -/
theorem prop_4_13_three_printed_false :
    grankHom [1, 1] [2] ≠ qMulti [1, 1] * qMulti [2] ∧
      invert (grankHom [1, 1] [2]) ≠ qMulti [1, 1] * qMulti [2] := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd ((grankHom_eq_printed_iff _ _).mp h) (by decide)
  · exact absurd ((invert_grankHom_eq_printed_iff _ _).mp h) (by decide)

/-! ## The matrix units -/

attribute [local instance] TBN.module

open Classical in
/-- The matrix unit `E_{ij} : Z_a → Z_b`, `b_i ↦ b'_j`, `b_{i'} ↦ 0` for `i' ≠ i`. -/
def matrixUnit (a b : List ℕ) (N : ℕ) (ha : blocksN a = N) (hb : blocksN b = N) (i : Idx a)
    (j : Idx b) : TBN a N ha →ₗ[(OLam N)ᵐᵒᵖ] TBN b N hb :=
  (basisTBN a N ha).constr ℕ fun i' => if i' = i then basisTBN b N hb j else 0

open Classical in
theorem matrixUnit_basis (a b : List ℕ) (N : ℕ) (ha : blocksN a = N) (hb : blocksN b = N)
    (i : Idx a) (j : Idx b) (i' : Idx a) :
    matrixUnit a b N ha hb i j (basisTBN a N ha i') = if i' = i then basisTBN b N hb j else 0 := by
  rw [matrixUnit, Module.Basis.constr_basis]

end

end OddMath.Frontier.EQBlocks
