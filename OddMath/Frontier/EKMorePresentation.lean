import OddMath.Frontier.SmallRankLimit
import OddMath.Frontier.EKPresentation
import OddMath.Frontier.OnhStructure

/-!
# [EK] §1, p. 3: the presentation of `Λ₋₁(n)`

Source: A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
arXiv:1107.5610v2, §1, p. 3: the ring `Λ₋₁(n)` has generators `e₁, …, e_n` and defining
relations
  `e_i e_j = e_j e_i` if `i + j` is even,
  `e_i e_j + (−1)^i e_j e_i = e_{j−1} e_{i+1} + (−1)^i e_{i+1} e_{j−1}` if `i + j` is odd,
and the odd nilHecke algebra is isomorphic to the matrix algebra of size `n!` over `Λ₋₁(n)`.

Here `LamN n` is the ring presented by generators `e₁, …, e_n` and exactly these relations for
`1 ≤ i, j ≤ n`, with the conventions `e₀ = 1` and `e_m = 0` for `m > n` (`eF`).

* `presentationEquivN n : LamN n ≃+* Λ/⟨e_m : m > n⟩`, `e_i ↦ e_i`, for every `n ≥ 0`
  (`presentationEquivN_e`), where `Λ = Q` is the integral odd symmetric functions.
* `ek_p3_presentation n : LamN n ≃+* OΛ_n` onto the odd symmetric polynomials in `n` variables
  (`SmallRank.OLam n`; this is `OΛ_n = ℤ` for `n = 0`, `ℤ[x]` for `n = 1`, and
  `OddSymmetricKernel.kernelSubring` for `n ≥ 2`), with `e_i ↦ ε_i`
  (`ek_p3_presentation_e`). This composes the above with EKL (5.3) in every rank
  (`SmallRank.equation_5_3_all`).
* `ek_p3_onh_matrix n`: `ONH_{n+2} ≅ Mat_{(n+2)!}(Λ₋₁(n+2))` (with `OnhStructure.card_Idx`).

The relations of `Λ₋₁(n)` at all `i, j ≥ 0` (`relation_even_all`, `relation_odd_all`) follow from
those with `1 ≤ i, j ≤ n`, since the odd relation for `(i, j)` coincides with the one for
`(j − 1, i + 1)`.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace OddMath.Frontier.EKMore
open EKRadicalQuotient (Q pi)
open OddSymmetricLimit (elemIdeal)
open CompleteElementary (A)

variable (n : ℕ)

/-- The free algebra on `e₁, …, e_n`. -/
abbrev FreeE := FreeAlgebra ℤ (Fin n)

/-- `e_m` in the free algebra, with `e₀ = 1` and `e_m = 0` for `m > n`. -/
def eF (m : ℕ) : FreeE n :=
  if h0 : m = 0 then 1 else if h : m ≤ n then FreeAlgebra.ι ℤ (⟨m - 1, by omega⟩ : Fin n) else 0

/-- The printed defining relations, `1 ≤ i, j ≤ n`. -/
inductive PRel : FreeE n → Prop
  | even (i j : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) (h : Even (i + j)) :
      PRel (eF n i * eF n j - eF n j * eF n i)
  | odd (i j : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n) (h : Odd (i + j)) :
      PRel (eF n i * eF n j + (-1 : ℤ) ^ i • (eF n j * eF n i) -
        (eF n (j - 1) * eF n (i + 1) + (-1 : ℤ) ^ i • (eF n (i + 1) * eF n (j - 1))))

/-- The ideal of relations. -/
def relIdealN : TwoSidedIdeal (FreeE n) := TwoSidedIdeal.span {r | PRel n r}

/-- `Λ₋₁(n)`: generators `e₁, …, e_n`, relations `PRel`. -/
abbrev LamN := FreeE n ⧸ (relIdealN n).asIdeal

/-- The quotient map. -/
def mkN : FreeE n →+* LamN n := Ideal.Quotient.mk _

/-- `e_m ∈ Λ₋₁(n)`. -/
def eL (m : ℕ) : LamN n := mkN n (eF n m)

theorem eF_zero : eF n 0 = 1 := by simp [eF]

theorem eF_big {m : ℕ} (hm : n < m) : eF n m = 0 := by
  unfold eF; rw [dif_neg (by omega), dif_neg (by omega)]

theorem eF_succ {i : ℕ} (hi : i < n) : eF n (i + 1) = FreeAlgebra.ι ℤ (⟨i, hi⟩ : Fin n) := by
  unfold eF; rw [dif_neg (by omega), dif_pos (by omega)]; rfl

theorem eL_zero : eL n 0 = 1 := by simp [eL, eF_zero, mkN]

theorem eL_big {m : ℕ} (hm : n < m) : eL n m = 0 := by simp [eL, eF_big n hm, mkN]

theorem prel_zero {r : FreeE n} (hr : PRel n r) : mkN n r = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (TwoSidedIdeal.mem_asIdeal.mpr (TwoSidedIdeal.subset_span hr))

theorem rel_even {i j : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (h : Even (i + j)) : eL n i * eL n j = eL n j * eL n i := by
  have := prel_zero n (PRel.even i j hi hin hj hjn h)
  simpa only [map_sub, map_mul, sub_eq_zero] using this

theorem rel_odd {i j : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (h : Odd (i + j)) : eL n i * eL n j + (-1 : ℤ) ^ i • (eL n j * eL n i) =
      eL n (j - 1) * eL n (i + 1) + (-1 : ℤ) ^ i • (eL n (i + 1) * eL n (j - 1)) := by
  have := prel_zero n (PRel.odd i j hi hin hj hjn h)
  simpa only [map_sub, map_add, map_mul, map_zsmul, sub_eq_zero] using this

theorem neg_one_pow_eq_of_even {a b : ℕ} (h : Even (a + b)) : (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  rcases Nat.even_or_odd a with ha | ha
  · have hb : Even b := (Nat.even_add.mp h).mp ha
    rw [ha.neg_one_pow, hb.neg_one_pow]
  · have hb : Odd b := by
      rcases Nat.even_or_odd b with hb | hb
      · exact absurd ((Nat.even_add.mp h).mpr hb) (Nat.not_even_iff_odd.mpr ha)
      · exact hb
    rw [ha.neg_one_pow, hb.neg_one_pow]

/-- The even relation for all `a, b ≥ 0`. -/
theorem relation_even_all (a b : ℕ) (h : Even (a + b)) : eL n a * eL n b = eL n b * eL n a := by
  by_cases ha0 : a = 0
  · subst ha0; simp [eL_zero]
  by_cases hb0 : b = 0
  · subst hb0; simp [eL_zero]
  by_cases han : n < a
  · simp [eL_big n han]
  by_cases hbn : n < b
  · simp [eL_big n hbn]
  exact rel_even n (by omega) (by omega) (by omega) (by omega) h

/-- The odd relation (2.12) in the form of `EKPresentation.Relator.odd`, for all `a ≥ 0`, `b > 0`. -/
theorem relation_odd_all (a b : ℕ) (hb : 0 < b) (h : Odd (a + b)) :
    eL n a * eL n b + (-1 : ℤ) ^ a • (eL n b * eL n a) =
      (-1 : ℤ) ^ a • (eL n (a + 1) * eL n (b - 1)) + eL n (b - 1) * eL n (a + 1) := by
  by_cases han : n < a
  · simp [eL_big n han, eL_big n (show n < a + 1 by omega)]
  by_cases hbn : n + 1 < b
  · simp [eL_big n (show n < b by omega), eL_big n (show n < b - 1 by omega)]
  by_cases hbe : b = n + 1
  · -- `e_b = 0`; the right side vanishes by the relation for `(n, a+1)`.
    subst hbe
    simp only [eL_big n (show n < n + 1 by omega), mul_zero, zero_mul, smul_zero, add_zero,
      Nat.add_sub_cancel]
    by_cases han' : a = n
    · subst han'; simp [eL_big a (show a < a + 1 by omega)]
    have hr := rel_odd n (i := n) (j := a + 1) (by omega) le_rfl (by omega) (by omega)
      (by rw [Nat.odd_iff] at h ⊢; omega)
    rw [Nat.add_sub_cancel, eL_big n (show n < n + 1 by omega), mul_zero, zero_mul, smul_zero,
      add_zero] at hr
    have hs : (-1 : ℤ) ^ a = (-1 : ℤ) ^ n :=
      neg_one_pow_eq_of_even (by rw [Nat.even_iff]; rw [Nat.odd_iff] at h; omega)
    rw [hs, eq_neg_of_add_eq_zero_left hr]
    abel
  have hbn' : b ≤ n := by omega
  by_cases ha0 : a = 0
  · subst ha0
    simp only [eL_zero, pow_zero, one_smul, mul_one, one_mul, zero_add]
    by_cases hb1 : b = 1
    · subst hb1; simp [eL_zero]
    have hr := rel_odd n (i := b - 1) (j := 1) (by omega) (by omega) le_rfl (by omega)
      (by rw [Nat.odd_iff] at h ⊢; omega)
    rw [show b - 1 + 1 = b by omega, Nat.sub_self, eL_zero, one_mul, mul_one] at hr
    have hs : (-1 : ℤ) ^ (b - 1) = 1 :=
      Even.neg_one_pow (by rw [Nat.even_iff]; rw [Nat.odd_iff] at h; omega)
    simp only [hs, one_smul] at hr
    rw [← hr]
    abel
  have hr := rel_odd n (i := a) (j := b) (by omega) (by omega) (by omega) hbn' h
  rw [hr]
  abel

/-! ## The map to `Λ/⟨e_m : m > n⟩` -/

/-- The quotient map `Λ → Λ/⟨e_m : m > n⟩`. -/
def mkE : Q →+* Q ⧸ (elemIdeal n).asIdeal := Ideal.Quotient.mk _

theorem mkE_e_big {m : ℕ} (hm : n < m) : mkE n (EKElementaryQuotient.e m) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [TwoSidedIdeal.mem_asIdeal]
  exact TwoSidedIdeal.subset_span ⟨m, hm, rfl⟩

theorem e_zero' : EKElementaryQuotient.e 0 = 1 := by
  simp [EKElementaryQuotient.e]

/-- The free map `e_i ↦ e_i`. -/
def freeToQuot : FreeE n →+* Q ⧸ (elemIdeal n).asIdeal :=
  (FreeAlgebra.lift ℤ fun i : Fin n => mkE n (EKElementaryQuotient.e (i.val + 1))).toRingHom

theorem freeToQuot_eF (m : ℕ) : freeToQuot n (eF n m) = mkE n (EKElementaryQuotient.e m) := by
  by_cases h0 : m = 0
  · subst h0; rw [eF_zero, map_one, e_zero', map_one]
  by_cases hm : n < m
  · rw [eF_big n hm, map_zero, mkE_e_big n hm]
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  rw [eF_succ n (by omega)]
  simp [freeToQuot]

theorem gen_true (m : ℕ) : pi (EKMixedPairing.gen true m) = EKElementaryQuotient.e m := rfl

open EKElementaryQuotient (e) in
theorem quot_odd (i j : ℕ) (hj : 1 ≤ j) (h : Odd (i + j)) :
    mkE n (e i) * mkE n (e j) + (-1 : ℤ) ^ i • (mkE n (e j) * mkE n (e i)) -
      (mkE n (e (j - 1)) * mkE n (e (i + 1)) +
        (-1 : ℤ) ^ i • (mkE n (e (i + 1)) * mkE n (e (j - 1)))) = 0 := by
  have he : Even (i + (j - 1)) := by
    rw [Nat.even_iff]; rw [Nat.odd_iff] at h; omega
  have key := EKQuotientRelations.same_odd_succ true i (j - 1) he
  rw [show j - 1 + 1 = j by omega] at key
  simp only [gen_true] at key
  have key3 := congrArg (mkE n) key
  simp only [map_add, map_mul, map_zsmul] at key3
  rw [key3]
  abel

theorem freeToQuot_killed (r : FreeE n) (hr : r ∈ (relIdealN n).asIdeal) : freeToQuot n r = 0 := by
  rw [relIdealN, TwoSidedIdeal.mem_asIdeal] at hr
  induction hr using TwoSidedIdeal.span_induction with
  | mem x hx =>
    cases hx with
    | even i j _ _ _ _ h =>
      rw [map_sub, map_mul, map_mul, freeToQuot_eF, freeToQuot_eF, sub_eq_zero, ← map_mul,
        ← map_mul]
      congr 1
      simpa only [gen_true] using EKQuotientRelations.same_even true i j h
    | odd i j _ _ hj _ h =>
      rw [map_sub, map_add, map_add, map_zsmul, map_zsmul, map_mul, map_mul, map_mul, map_mul,
        freeToQuot_eF, freeToQuot_eF, freeToQuot_eF, freeToQuot_eF]
      exact quot_odd n i j hj h
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, hx, mul_zero]
  | right_absorb a x _ hx => rw [map_mul, hx, zero_mul]

/-- `Λ₋₁(n) → Λ/⟨e_m : m > n⟩`. -/
def toQuot : LamN n →+* Q ⧸ (elemIdeal n).asIdeal :=
  Ideal.Quotient.lift _ (freeToQuot n) (freeToQuot_killed n)

theorem toQuot_eL (m : ℕ) : toQuot n (eL n m) = mkE n (EKElementaryQuotient.e m) := by
  rw [eL, mkN, toQuot, Ideal.Quotient.lift_mk, freeToQuot_eF]

/-! ## The inverse map -/

/-- `h_m ↦ e_m` from the free algebra on the `h`'s. -/
def freeToLam : A →+* LamN n := (FreeAlgebra.lift ℤ fun i : ℕ => eL n (i + 1)).toRingHom

theorem freeToLam_h (m : ℕ) : freeToLam n (CompleteElementary.h m) = eL n m := by
  cases m with
  | zero => rw [CompleteElementary.h_zero, map_one, eL_zero]
  | succ m => simp [freeToLam, CompleteElementary.h]

theorem freeToLam_killed (r : A) (hr : r ∈ EKPresentation.relIdeal) : freeToLam n r = 0 := by
  rw [EKPresentation.relIdeal, EKPresentation.relTwoSided, TwoSidedIdeal.mem_asIdeal] at hr
  induction hr using TwoSidedIdeal.span_induction with
  | mem x hx =>
    cases hx with
    | even a b hab =>
      rw [map_sub, map_mul, map_mul, freeToLam_h, freeToLam_h, relation_even_all n a b hab, sub_self]
    | odd a b hb hab =>
      simp only [map_sub, map_add, map_mul, map_zsmul, freeToLam_h]
      rw [relation_odd_all n a b hb hab, sub_self]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, hx, mul_zero]
  | right_absorb a x _ hx => rw [map_mul, hx, zero_mul]

/-- `Λ → Λ₋₁(n)`, through the e-presentation of `Λ` (Corollary 2.13). -/
def qToLam : Q →+* LamN n :=
  (Ideal.Quotient.lift _ (freeToLam n) (freeToLam_killed n)).comp
    EKPresentation.elementaryPresentationEquiv.symm.toRingHom

theorem qToLam_e (m : ℕ) : qToLam n (EKElementaryQuotient.e m) = eL n m := by
  have h : EKPresentation.elementaryPresentationEquiv.symm (EKElementaryQuotient.e m) =
      EKPresentation.h m := by
    apply EKPresentation.elementaryPresentationEquiv.injective
    rw [RingEquiv.apply_symm_apply, EKPresentation.elementaryPresentationEquiv_apply,
      EKPresentation.toColor_h]
    rfl
  simp only [qToLam, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h]
  rw [EKPresentation.h, EKPresentation.mk, Ideal.Quotient.lift_mk, freeToLam_h]

theorem qToLam_killed (x : Q) (hx : x ∈ (elemIdeal n).asIdeal) : qToLam n x = 0 := by
  rw [TwoSidedIdeal.mem_asIdeal] at hx
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [qToLam_e, eL_big n hm]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | neg x _ hx => rw [map_neg, hx, neg_zero]
  | left_absorb a x _ hx => rw [map_mul, hx, mul_zero]
  | right_absorb a x _ hx => rw [map_mul, hx, zero_mul]

/-- `Λ/⟨e_m : m > n⟩ → Λ₋₁(n)`. -/
def toLam : Q ⧸ (elemIdeal n).asIdeal →+* LamN n :=
  Ideal.Quotient.lift _ (qToLam n) (qToLam_killed n)

theorem toLam_mkE (x : Q) : toLam n (mkE n x) = qToLam n x := Ideal.Quotient.lift_mk _ _ _

theorem toLam_toQuot : (toLam n).comp (toQuot n) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  have h : ((toLam n).comp (toQuot n)).comp (Ideal.Quotient.mk _) = mkN n := by
    apply RingHom.toIntAlgHom_injective
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, RingHom.toIntAlgHom_apply, RingHom.comp_apply]
    have e1 := toQuot_eL n (i.val + 1)
    rw [eL, eF_succ n i.isLt] at e1
    change toLam n (toQuot n (mkN n (FreeAlgebra.ι ℤ i))) = _
    rw [e1, toLam_mkE, qToLam_e, eL, eF_succ n i.isLt]
  rw [h]; rfl

theorem toQuot_toLam : (toQuot n).comp (toLam n) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  have hQ : ((toQuot n).comp (toLam n)).comp (Ideal.Quotient.mk _) = mkE n := by
    have hP : (((toQuot n).comp (toLam n)).comp (Ideal.Quotient.mk _)).comp
        (EKPresentation.elementaryPresentationEquiv.toRingHom.comp EKPresentation.mk) =
        (mkE n).comp (EKPresentation.elementaryPresentationEquiv.toRingHom.comp
          EKPresentation.mk) := by
      apply RingHom.toIntAlgHom_injective
      apply FreeAlgebra.hom_ext
      funext i
      simp only [Function.comp_apply, RingHom.toIntAlgHom_apply, RingHom.comp_apply]
      have hh : EKPresentation.elementaryPresentationEquiv.toRingHom
          (EKPresentation.mk (FreeAlgebra.ι ℤ i)) = EKElementaryQuotient.e (i + 1) := by
        change EKPresentation.elementaryPresentationEquiv (EKPresentation.h (i + 1)) = _
        rw [EKPresentation.elementaryPresentationEquiv_apply, EKPresentation.toColor_h]
        rfl
      rw [hh]
      change toQuot n (toLam n (mkE n _)) = _
      rw [toLam_mkE, qToLam_e, toQuot_eL]
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := EKPresentation.elementaryPresentationEquiv.surjective x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact RingHom.congr_fun hP z
  rw [hQ]; rfl

/-- [EK] p. 3: `Λ₋₁(n) ≅ Λ/⟨e_m : m > n⟩`, `e_i ↦ e_i`, for every `n`. -/
def presentationEquivN : LamN n ≃+* Q ⧸ (elemIdeal n).asIdeal :=
  RingEquiv.ofHomInv (toQuot n) (toLam n) (toLam_toQuot n) (toQuot_toLam n)

theorem presentationEquivN_e (m : ℕ) :
    presentationEquivN n (eL n m) = mkE n (EKElementaryQuotient.e m) := toQuot_eL n m

/-- [EK] p. 3: `Λ₋₁(n) ≅ OΛ_n`, the odd symmetric polynomials in `n` variables, for every `n`
(including `n = 0, 1`). -/
def ek_p3_presentation : LamN n ≃+* SmallRank.OLam n :=
  (presentationEquivN n).trans (SmallRank.equation_5_3_all n)

theorem ek_p3_presentation_e (m : ℕ) :
    (ek_p3_presentation n (eL n m) : OddMath.SkewPolynomial.SkewPolynomial n) =
      FiniteCompleteElementary.elementaryPoly n m := by
  rw [ek_p3_presentation, RingEquiv.trans_apply, presentationEquivN_e]
  rw [mkE, SmallRank.equation_5_3_all_mk, SmallRank.piAll_coe, OddLREKIdentification.piN_e]

/-- [EK] p. 3: `ONH_{n+2} ≅ Mat_{(n+2)!}(Λ₋₁(n+2))` (the index set has `(n+2)!` elements,
`OnhStructure.card_Idx`). -/
def ek_p3_onh_matrix :
    Matrix (OnhStructure.Idx n) (OnhStructure.Idx n) (LamN (n + 2)) ≃+* NilHeckeAction.Presented n :=
  ((ek_p3_presentation (n + 2)).trans (RingEquiv.refl _)).mapMatrix.trans
    (OnhStructure.matrixEquiv n)

end OddMath.Frontier.EKMore
