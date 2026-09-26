import OddMath.Frontier.EKRestCenter

/-! # The centre of `Λ` coincides with the supercentre

EK arXiv:1107.5610v2, §1 (p. 3) and §3.2 (p. 26): the even-degree primitives generate "the
center (which coincides with the supercenter)".

The supercentre of the `ℤ`-graded superalgebra `Λ` (parity = degree mod 2) is spanned by the
homogeneous `z` of degree `d` with `z y = (-1)^{de} y z` for all homogeneous `y` of degree `e`
(`SuperCentral`, `supercenter`). Integrally at q = -1 in the radical quotient `Q`:

* `superCentral_odd`: a supercentral element of odd degree is `0`;
* `supercenter_eq_center`: the supercentre equals the centre.

Route for odd degree `d = 2m+1`: in `OΛ_N`, `N = 2m+2`, the image `f` of `z` satisfies
`f w = (-1)^e w f` on homogeneous `w`, while `V = x₁⋯x_N` satisfies `V w = (-1)^e w V`; hence
`fV` is central in `OΛ_N`, so a polynomial in the squares (`CenterCorrected.center_oddSymmetric`).
But every exponent of `f` has a zero entry (`d < N`), which becomes an odd entry `1` of `fV`.
-/

noncomputable section
open scoped BigOperators

namespace OddMath.Frontier.EKRest
open EKRadicalQuotient EKIntegralBases DegreeShapes
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open OddLREKIdentification (piN)
open OddSymmetricLimit (piA piA_surjective piA_coe)

/-! ## Skew-polynomial sign bookkeeping -/

theorem crossingCount_swap {N : ℕ} (x y : Fin N → ℕ) :
    OddMath.crossingCount x y + OddMath.crossingCount y x + ∑ i, x i * y i =
      (∑ i, x i) * (∑ i, y i) := by
  classical
  have hsplit : ∀ i : Fin N, ∑ j, x i * y j =
      ∑ j ∈ Finset.univ.filter (fun j => j < i), x i * y j + x i * y i +
        ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * y j := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j < i)]
    have h2 : Finset.univ.filter (fun j => ¬ j < i) =
        insert i (Finset.univ.filter (fun j => i < j)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h; rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
        · right; exact h'
        · left; exact h'.symm
      · rintro (rfl | h) <;> [exact lt_irrefl _; exact not_lt.mpr h.le]
    rw [h2, Finset.sum_insert (by simp)]
    ring
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_comm (f := fun i j => x i * y j)] at *
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i)]
  simp only [Finset.sum_add_distrib, OddMath.crossingCount]
  have hsw : ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), x i * y j =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j < i), y i * x j := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.filter (fun i => i < j))]
    · apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    · intro i j; simp
  rw [hsw]
  ring

theorem skewSign_one_swap (m : ℕ) (a : Fin (2 * m + 2) → ℕ) :
    OddMath.skewSign (fun _ => 1) a = (-1 : ℤ) ^ (∑ i, a i) * OddMath.skewSign a (fun _ => 1) := by
  have h := crossingCount_swap (fun _ : Fin (2 * m + 2) => 1) a
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at h
  have h2 : OddMath.crossingCount (fun _ => 1) a =
      (2 * m + 1) * (∑ i, a i) - OddMath.crossingCount a (fun _ => 1) := by
    have : (2 * m + 2) * ∑ i, a i = (2 * m + 1) * (∑ i, a i) + ∑ i, a i := by ring
    omega
  have hle : OddMath.crossingCount a (fun _ => 1) ≤ (2 * m + 1) * (∑ i, a i) := by
    have : (2 * m + 2) * ∑ i, a i = (2 * m + 1) * (∑ i, a i) + ∑ i, a i := by ring
    omega
  unfold OddMath.skewSign
  rw [h2, ← pow_add]
  apply neg_one_pow_congr
  rw [Nat.even_iff, Nat.even_iff]
  have : (2 * m + 1) * ∑ i, a i = 2 * (m * ∑ i, a i) + ∑ i, a i := by ring
  omega

/-- `V w = (-1)^e w V` for `w` homogeneous of degree `e`, `N = 2m + 2`. -/
theorem V_mul_homogeneous (m e : ℕ) (w : SkewPolynomial (2 * m + 2))
    (hw : ElementaryBasis.Homogeneous e w) :
    CenterPoly.V (2 * m) * w = (-1 : ℤ) ^ e • (w * CenterPoly.V (2 * m)) := by
  rw [CenterPoly.V_eq_monomial, CenterPoly.mul_monomial_left, CenterPoly.mul_monomial_right,
    Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro a ha
  have hwa : ∑ i, a i = e := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp ha) (hw a hne)
  rw [skewSign_one_swap, hwa, show (fun _ => 1) + a = a + (fun _ => 1) from add_comm _ _,
    OddMath.SkewPolynomial.monomial, OddMath.SkewPolynomial.monomial, Finsupp.smul_single,
    smul_eq_mul]
  congr 1
  ring

/-! ## Odd degree -/

/-- Homogeneous supercentral elements (degree `d`). -/
def SuperCentral (d : ℕ) (z : Q) : Prop :=
  z ∈ degreePiece d ∧ ∀ e, ∀ y ∈ degreePiece e, z * y = (-1 : ℤ) ^ (d * e) • (y * z)

/-- EK p. 26: a supercentral element of odd degree is `0`. -/
theorem superCentral_odd (m : ℕ) (z : Q) (hz : SuperCentral (2 * m + 1) z) : z = 0 := by
  classical
  obtain ⟨hzd, hsc⟩ := hz
  set f := piN (2 * m + 2) z with hf
  have hfhom : ElementaryBasis.Homogeneous (2 * m + 1) f :=
    OddSymmetricLimit.piN_homogeneous (2 * m + 2) (2 * m + 1) ⟨z, hzd⟩
  -- `f` super-commutes with the image of every homogeneous element
  have hsup : ∀ e, ∀ y ∈ degreePiece e, f * piN (2 * m + 2) y =
      (-1 : ℤ) ^ e • (piN (2 * m + 2) y * f) := by
    intro e y hy
    rw [hf, ← map_mul, hsc e y hy, map_zsmul, map_mul]
    congr 1
    rw [pow_mul]
    have : ((-1 : ℤ) ^ (2 * m + 1)) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [this]
  -- `g = f V` is central in `OΛ_N`
  let g : OddSymmetricKernel.kernelSubring (2 * m) :=
    piA (2 * m) z * ⟨CenterPoly.V (2 * m), CenterPoly.V_mem_kernel⟩
  have hgc : g ∈ Subring.center (OddSymmetricKernel.kernelSubring (2 * m)) := by
    rw [Subring.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := piA_surjective (2 * m) w
    apply Subtype.ext
    simp only [g, Subring.coe_mul, piA_coe]
    have key : ∀ e, piN (2 * m + 2) (decompose y e) * (f * CenterPoly.V (2 * m)) =
        f * CenterPoly.V (2 * m) * piN (2 * m + 2) (decompose y e) := by
      intro e
      have hye := decompose_mem y e
      have h1 : CenterPoly.V (2 * m) * piN (2 * m + 2) (decompose y e) =
          (-1 : ℤ) ^ e • (piN (2 * m + 2) (decompose y e) * CenterPoly.V (2 * m)) :=
        V_mul_homogeneous m e _ (OddSymmetricLimit.piN_homogeneous (2 * m + 2) e ⟨_, hye⟩)
      have h2 := hsup e _ hye
      symm
      calc f * CenterPoly.V (2 * m) * piN (2 * m + 2) (decompose y e)
          = f * (CenterPoly.V (2 * m) * piN (2 * m + 2) (decompose y e)) := mul_assoc _ _ _
        _ = (-1 : ℤ) ^ e • (f * piN (2 * m + 2) (decompose y e) * CenterPoly.V (2 * m)) := by
          rw [h1, mul_smul_comm, mul_assoc]
        _ = (-1 : ℤ) ^ e • ((-1 : ℤ) ^ e • (piN (2 * m + 2) (decompose y e) * f) *
            CenterPoly.V (2 * m)) := by rw [h2]
        _ = piN (2 * m + 2) (decompose y e) * f * CenterPoly.V (2 * m) := by
          rw [smul_mul_assoc, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow,
            one_smul]
        _ = piN (2 * m + 2) (decompose y e) * (f * CenterPoly.V (2 * m)) := mul_assoc _ _ _
    rw [← hf]
    conv_lhs => rw [← recompose_decompose y]
    conv_rhs => rw [← recompose_decompose y]
    rw [recompose_apply, Finsupp.sum, map_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun e _ => key e)
  obtain ⟨a, ha, b, _, heq⟩ :=
    (CenterCorrected.center_oddSymmetric (2 * m) g).mp hgc
  have hodd : ¬ Odd (2 * m + 2) := by
    rw [Nat.not_odd_iff_even]; exact ⟨m + 1, by ring⟩
  rw [if_neg hodd, add_zero] at heq
  obtain ⟨P, _, hPa⟩ := (CenterPoly.mem_sq _).mp ha
  have hf0 : f = 0 := by
    ext c
    rw [Finsupp.coe_zero, Pi.zero_apply]
    rcases eq_or_ne (f c) 0 with h0 | hc
    · exact h0
    exfalso
    have hwc : ∑ i, c i = 2 * m + 1 := by
      rcases eq_or_ne (∑ i, c i) (2 * m + 1) with h | hne
      · exact h
      · exact absurd (hfhom c hne) hc
    obtain ⟨j, hj⟩ : ∃ j, c j = 0 := by
      rcases Classical.em (∃ j, c j = 0) with h | hall
      · exact h
      exfalso
      push_neg at hall
      have : ∑ i, (1 : ℕ) ≤ ∑ i, c i := Finset.sum_le_sum (fun i _ => Nat.one_le_iff_ne_zero.mpr (hall i))
      simp at this
      omega
    have hg1 : (g : SkewPolynomial (2 * m + 2)) (c + fun _ => 1) =
        f c * OddMath.skewSign c (fun _ => 1) := by
      simp only [g, Subring.coe_mul, piA_coe, CenterPoly.V_eq_monomial,
        CenterPoly.mul_monomial_right]
      rw [CenterPoly.sum_translate_apply _ _ _ (fun _ r => r * 1 * OddMath.skewSign _ _)
        (fun _ => by simp)]
      rw [mul_one]
    have hg0 : (g : SkewPolynomial (2 * m + 2)) (c + fun _ => 1) = 0 := by
      rw [heq, ← hPa]
      apply CenterPoly.squareHom_apply_of_not_even P _ j
      simp [hj]
    rw [hg0] at hg1
    have hs : OddMath.skewSign c (fun _ => 1) ≠ 0 := by
      unfold OddMath.skewSign; exact pow_ne_zero _ (by norm_num)
    rcases mul_eq_zero.mp hg1.symm with h | h
    · exact hc h
    · exact hs h
  apply congrArg Subtype.val (OddSymmetricLimit.degreeMap_injective (2 * m) (2 * m + 1) (by omega)
    (a₁ := ⟨z, hzd⟩) (a₂ := 0) ?_)
  apply Subtype.ext
  simp only [OddSymmetricLimit.degreeMap_coe, map_zero, ZeroMemClass.coe_zero]
  exact hf0

/-! ## Supercentre = centre -/

/-- The supercentre: the span of the homogeneous supercentral elements. -/
def supercenter : Submodule ℤ Q := Submodule.span ℤ {z | ∃ d, SuperCentral d z}

theorem superCentral_central {d : ℕ} {z : Q} (hz : SuperCentral d z) : z ∈ Subring.center Q := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
  · apply central_of_hPartition
    intro μ
    rw [hz.2 _ _ (hPartition_mem' μ), mul_assoc, pow_mul]
    simp
  · rw [superCentral_odd m z hz]; exact Subring.zero_mem _

theorem central_superCentral {d : ℕ} {z : Q} (hzd : z ∈ degreePiece d)
    (hz : z ∈ Subring.center Q) : SuperCentral d z := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
  · refine ⟨hzd, fun e y _ => ?_⟩
    rw [mul_assoc, pow_mul]
    simp [(Subring.mem_center_iff.mp hz y).symm]
  · rw [center_odd m z hzd hz]
    exact ⟨Submodule.zero_mem _, fun e y _ => by simp⟩

/-- **EK pp. 3, 26: the centre of `Λ` coincides with the supercentre.** -/
theorem supercenter_eq_center : (supercenter : Set Q) = Subring.center Q := by
  ext z
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨d, hd⟩ := hx; exact superCentral_central hd
    | zero => exact Subring.zero_mem _
    | add x y _ _ hx hy => exact Subring.add_mem _ hx hy
    | smul c x _ hx => exact Subring.zsmul_mem _ hx c
  · intro hz
    change z ∈ supercenter
    rw [← recompose_decompose z, recompose_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro d _
    exact Submodule.subset_span ⟨d, central_superCentral (decompose_mem z d)
      (decompose_central hz d)⟩

end OddMath.Frontier.EKRest
