import OddMath.Frontier.EQLimaLimit
import OddMath.Frontier.ElementaryRelations
import OddMath.Frontier.EKIntegralBases

/-!
# Ellis–Qi, Appendix A.1: `e_2²` is not a cocycle

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.1.3, the display before Proposition A.3: over a field of characteristic `2`,
`H(Sym)` is a polynomial algebra on `e_2², e_4², …` (see `EQPdg.cohomology_char_two`), but
"the naïve odd analogue of this statement is not true. For instance

  `d(e_2²) = -2 e_4 e_1 + 2 e_5 ≠ 0`,

so `e_2²` is not even a cocycle."

* `d_elementary_two_sq`: the identity `d(e_2²) = -2 e_4 e_1 + 2 e_5` in `OΛ_N ⊆ OPol_N`, for
  every `N` (untwisted elementary polynomials; `e_k = 0` for `k > N`). It follows from
  Lemma 3.2 (`d_elementary`) and the relations `e_1 e_{2m} + e_{2m} e_1 = 2 e_{2m+1}`,
  `e_3 e_2 - e_2 e_3 = e_1 e_4 - e_4 e_1` of odd symmetric polynomials.
* `DQ_e`: Lemma 3.2 in the limit `OΛ`: `d(e_k) = e_1 e_k - {k+1} e_{k+1}`.
* `DQ_e_two_sq`, `DQ_e_two_sq_ne_zero`: `d(e_2²) = -2 e_4 e_1 + 2 e_5 ≠ 0` in `OΛ` (the
  elementary monomials `e_4 e_1` and `e_5` are distinct elements of the basis `e_λ` of `OΛ`);
  `e_two_sq_not_cocycle`: `e_2²` is not a cocycle of `OΛ`.
-/

namespace OddMath.Frontier.EQLima

open OddMath.SkewPolynomial (SkewPolynomial)
open OddMath.Frontier.EQSkewDifferential (d theta parityInv elementary d_elementary d_mul
  parityInv_elementary)
open FiniteCompleteElementary (elementaryPoly)
open OddLREKIdentification (piN)
open EKElementaryQuotient (e)
open EKRadicalQuotient (Q)

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolNUNASemiringEQLimaNaive (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) opolNUNARingEQLimaNaive (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-- The computation of `d(e_2²)` from Lemma 3.2 and three relations, in any ring with a twisted
derivation. -/
theorem d_sq_aux {R : Type*} [Ring R] (D ι : R → R)
    (hD : ∀ x y, D (x * y) = D x * y + ι x * D y) (e1 e2 e3 e4 e5 : R)
    (h2 : D e2 = e1 * e2 - e3) (hι : ι e2 = e2)
    (r1 : e1 * e2 + e2 * e1 = (2 : ℤ) • e3)
    (r2 : e3 * e2 - e2 * e3 = -(e4 * e1) + e1 * e4)
    (r3 : e1 * e4 + e4 * e1 = (2 : ℤ) • e5) :
    D (e2 * e2) = (-2 : ℤ) • (e4 * e1) + (2 : ℤ) • e5 := by
  have h14 : e1 * e4 = (2 : ℤ) • e5 - e4 * e1 := eq_sub_of_add_eq r3
  have key : D (e2 * e2) = (e1 * e2 + e2 * e1) * e2 - e3 * e2 - e2 * e3 := by
    rw [hD, hι, h2]
    noncomm_ring
  have h3 : ((2 : ℤ) • e3) * e2 - e3 * e2 - e2 * e3 = e3 * e2 - e2 * e3 := by
    rw [two_smul, add_mul]
    abel
  rw [key, r1, h3, r2, h14]
  abel

theorem elementary_eq_theta (N k : ℕ) : elementary N k = theta N (elementaryPoly N k) := by
  rw [← theta_elementary, EQSchur.theta_theta]

/-- `e_1 e_{2m} + e_{2m} e_1 = 2 e_{2m+1}` for the untwisted elementary polynomials. -/
theorem elementary_one_even_untwisted (N m : ℕ) :
    elementary N 1 * elementary N (2 * m) + elementary N (2 * m) * elementary N 1 =
      (2 : ℤ) • elementary N (2 * m + 1) := by
  rw [elementary_eq_theta N 1, elementary_eq_theta N (2 * m), elementary_eq_theta N (2 * m + 1),
    ← map_mul, ← map_mul, ← map_add, ← map_zsmul, ElementaryRelations.elementary_one_even]

/-- `e_3 e_2 - e_2 e_3 = -e_4 e_1 + e_1 e_4` for the untwisted elementary polynomials. -/
theorem elementary_three_two_untwisted (N : ℕ) :
    elementary N 3 * elementary N 2 - elementary N 2 * elementary N 3 =
      -(elementary N 4 * elementary N 1) + elementary N 1 * elementary N 4 := by
  have h := congrArg (theta N) (ElementaryRelations.elementary_odd N 3 1 (by decide))
  have hs : ((-1 : ℤ) ^ 3) = -1 := by norm_num
  rw [map_add, map_add, map_zsmul, map_zsmul, map_mul, map_mul, map_mul, map_mul, hs, neg_smul,
    neg_smul, one_smul, one_smul] at h
  rw [sub_eq_add_neg]
  simpa only [← elementary_eq_theta, Nat.reduceAdd] using h

/-- **`d(e_2²) = -2 e_4 e_1 + 2 e_5`** in `OΛ_N`, every `N` (Ellis–Qi, Appendix A.1.3). -/
theorem d_elementary_two_sq (N : ℕ) :
    d N (elementary N 2 * elementary N 2) =
      (-2 : ℤ) • (elementary N 4 * elementary N 1) + (2 : ℤ) • elementary N 5 := by
  refine d_sq_aux (d N) (parityInv N) (fun x y => d_mul x y) (elementary N 1) (elementary N 2)
    (elementary N 3) (elementary N 4) (elementary N 5) ?_ ?_ ?_
    (elementary_three_two_untwisted N) ?_
  · have h := d_elementary (n := N) 2
    have hc : (((2 + 1) % 2 : ℕ) : ℤ) = 1 := by norm_num
    rw [hc, one_smul] at h
    exact h
  · rw [parityInv_elementary]
    norm_num
  · exact elementary_one_even_untwisted N 1
  · exact elementary_one_even_untwisted N 2

/-- **Lemma 3.2 in the limit `OΛ`**: `d(e_k) = e_1 e_k - {k+1} e_{k+1}`. -/
theorem DQ_e (k : ℕ) : DQ (e k) = e 1 * e k - (((k + 1) % 2 : ℕ) : ℤ) • e (k + 1) := by
  refine eq_of_piN fun n => ?_
  rw [piN_DQ, map_sub, map_mul, map_zsmul]
  simp only [OddLREKIdentification.piN_e]
  rw [dt_apply, ← elementary_eq_theta, d_elementary, map_sub, map_mul, map_zsmul]
  simp only [theta_elementary]

/-- **`d(e_2²) = -2 e_4 e_1 + 2 e_5`** in `OΛ` (Ellis–Qi, Appendix A.1.3). -/
theorem DQ_e_two_sq : DQ (e 2 * e 2) = (-2 : ℤ) • (e 4 * e 1) + (2 : ℤ) • e 5 := by
  refine eq_of_piN fun n => ?_
  rw [piN_DQ, map_mul (piN (n + 2)), dt_apply]
  simp only [OddLREKIdentification.piN_e, map_add, map_zsmul, map_mul (piN (n + 2))]
  rw [map_mul (theta (n + 2)), ← elementary_eq_theta, d_elementary_two_sq, map_add, map_zsmul,
    map_zsmul, map_mul (theta (n + 2))]
  simp only [theta_elementary]

/-- `(4,1)`. -/
def yd41 : YoungDiagram := YoungDiagram.ofRowLens [4, 1] (by decide)

/-- `(5)`. -/
def yd5 : YoungDiagram := YoungDiagram.ofRowLens [5] (by decide)

theorem eBasis_yd41 : EKIntegralBases.eBasis yd41 = e 4 * e 1 := by
  rw [EKIntegralBases.eBasis_apply, EKPartitionSpanning.ePartition, yd41,
    YoungDiagram.rowLens_ofRowLens_eq_self (by decide)]
  simp

theorem eBasis_yd5 : EKIntegralBases.eBasis yd5 = e 5 := by
  rw [EKIntegralBases.eBasis_apply, EKPartitionSpanning.ePartition, yd5,
    YoungDiagram.rowLens_ofRowLens_eq_self (by decide)]
  simp

theorem yd41_ne_yd5 : yd41 ≠ yd5 := by
  intro h
  have h1 := congrArg YoungDiagram.rowLens h
  rw [yd41, yd5, YoungDiagram.rowLens_ofRowLens_eq_self (by decide),
    YoungDiagram.rowLens_ofRowLens_eq_self (by decide)] at h1
  exact absurd h1 (by decide)

/-- `-2 e_4 e_1 + 2 e_5 ≠ 0` in `OΛ`: `e_4 e_1` and `e_5` are distinct elements of the basis of
elementary monomials. -/
theorem neg_two_e_four_one_add_ne_zero : (-2 : ℤ) • (e 4 * e 1) + (2 : ℤ) • e 5 ≠ 0 := by
  intro h0
  rw [← eBasis_yd41, ← eBasis_yd5] at h0
  have h1 := congrArg (fun x => EKIntegralBases.eBasis.repr x yd5) h0
  simp only [map_add, map_zsmul, Module.Basis.repr_self, map_zero, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
  rw [Finsupp.single_eq_of_ne' yd41_ne_yd5] at h1
  norm_num at h1

/-- **`d(e_2²) ≠ 0` in `OΛ`** (Ellis–Qi, Appendix A.1.3). -/
theorem DQ_e_two_sq_ne_zero : DQ (e 2 * e 2) ≠ 0 := by
  rw [DQ_e_two_sq]
  exact neg_two_e_four_one_add_ne_zero

/-- `e_2²` is not a cocycle of the dg algebra `OΛ`: the naïve odd analogue of
`H(Sym) = 𝕜[e_2², e_4², …]` (characteristic `2`) fails. -/
theorem e_two_sq_not_cocycle : e 2 * e 2 ∉ dataQ.cocycles :=
  fun h => DQ_e_two_sq_ne_zero h

end

end OddMath.Frontier.EQLima
