/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Envelope
import OddMath.QuiverHecke.CategoricalDividedPowersOdd

/-!
# Words, `P(i^{(n)})` and Lemma 11.1 in `K₀(Ḣ_{q,π})`

Brundan–Ellis, arXiv:1701.04133v2, §11: Lemma 11.1 (`H_n 1_{iⁿ} ≅ P(i^{(n)})^{⊕[n]^!_{q_i,π_i}}`)
and the projectives `P(i^{(n)})` of (11.3), read in the envelope `Ḣ_{q,π}` of
`OddMath.QuiverHecke.Envelope`.

* `HKar`: the 1-morphism category of `Ḣ_{q,π}`, written as the completed hom category of
  `OddMath.SKM.Summands` (definitionally `HCat`, `hKar_eq`); the classes below live in its split
  Grothendieck group.
* `word t`: the word `t` as a 1-morphism of `Ḣ_{q,π}` (the projective `H_n 1_t`).
* `dividedPowerEven i hi r`, `dividedPowerOdd i hi n`: the summand of `iʳ` cut out by BE2's
  divided-power idempotent `1_{i^{(r)}} = D_{w₀}` (`evenCornerProjector`, `oddCornerProjector`),
  shifted so that Lemma 11.1 holds with the balanced factorial:
  `[iʳ] = [r]^!_{q_i} [dividedPowerEven i hi r]` (`class_word_even`) and
  `[i^{n+2}] = [n+2]^!_{q_i,π} [dividedPowerOdd i hi n]` (`class_word_odd`).

The shift is `Q^{d_i r(r-1)/2}` for an even colour and `Q^{d_i C} Π^C`, `C = (n+2)(n+1)/2`, for
an odd colour. These are the shifts of BE2's `E_i^{(n)} 1_λ` as corrected in ERRATA [BE2] 13
(the categorical divided powers of Lemma 11.5 are the images of these objects); in the envelope
the 1-morphism `iʳ` stands for the projective `H_r 1_{iʳ}` contravariantly in the shift, which is
why the shift `Q^{-d_i r(r-1)/2}` of (11.3) appears with the opposite sign. With the printed
shifts the factorial in Lemma 11.1 is not balanced (`class_word_even_unshifted`).
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams GradedSupercategory OddMath.SKM.Summands
open CategoryTheory.Idempotents LaurentPolynomial
open OddMath.Frontier OddMath.SKM.DividedPowerDecomposition OddMath.SKM.DividedPowerIdempotents
open OddMath.QuiverHecke.DividedPowerModules OddMath.CoveringQuantum BoxPartitionCount
open OddMath.QuiverHecke.CategoricalDividedPowers Categorification Categorification.KLR

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)
  (hc : Sc.Homogeneous)

/-- The object of `H` attached to a word. -/
abbrev hObj (t : List I) : HGr D Sc sy hc := (pres D Sc).obj (ob D t)

/-- The graded super Karoubi envelope of `H`, written as the completed hom category of
`OddMath.SKM.Summands`; it is the 1-morphism category `HCat` of `Ḣ_{q,π}` (`hKar_eq`). -/
abbrev HKar := Karoubi (Mat_ (Base k (HGr D Sc sy hc)))

theorem hKar_eq : HKar (k := k) D Sc sy hc = HCat D Sc sy hc := rfl

/-- **BE2 §11.** The word `t` as a 1-morphism of `Ḣ_{q,π}`. -/
abbrev word (t : List I) : HKar D Sc sy hc := whole (k := k) (hObj D Sc sy hc t)

/-! ### Even colours -/

section Even

variable (i : I) (hi : D.parity i = 0) (r : ℕ)

theorem evenCornerProjector_degree :
    (evenCornerProjector D Sc i hi r :
      hObj D Sc sy hc (List.replicate r i) ⟶ hObj D Sc sy hc (List.replicate r i)) ∈
      degree (R := k) (C := HGr D Sc sy hc) _ _ 0 :=
  evenNilHecke_demIdem_mem D Sc hi r (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy)

theorem evenCornerProjector_even :
    (evenCornerProjector D Sc i hi r :
      hObj D Sc sy hc (List.replicate r i) ⟶ hObj D Sc sy hc (List.replicate r i)) ∈
      Supercategory.parity (R := k) (C := HGr D Sc sy hc) _ _ 0 :=
  evenNilHecke_demIdem_mem D Sc hi r (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi)

/-- The summand `Q^m (iʳ, 1_{i^{(r)}})` of `Ḣ_{q,π}`. -/
abbrev evenSummand (m : ℤ) : HKar D Sc sy hc :=
  raw (f := hObj D Sc sy hc (List.replicate r i))
    (evenCornerProjector_idempotent D Sc i hi r).eq
    (evenCornerProjector_degree D Sc sy hc i hi r) (evenCornerProjector_even D Sc sy hc i hi r)
    m 0

/-- **BE2 (11.3), even colour.** The divided power `P(i^{(r)})` in `Ḣ_{q,π}`. -/
abbrev dividedPowerEven : HKar D Sc sy hc :=
  evenSummand D Sc sy hc i hi r ((r.choose 2 : ℤ) * sy.d i)

/-- The splitting of Lemma 11.1 in `Ḣ_{q,π}`: `[iʳ] = ∑_j [Q^{d_i s_j} (iʳ, 1_{i^{(r)}})]`. -/
theorem class_word_summands_even :
    K₀.mk (word D Sc sy hc (List.replicate r i)) =
      ∑ j : evenIndex r, K₀.mk (evenSummand D Sc sy hc i hi r (evenShift r j * sy.d i)) := by
  let S := evenCornerSplitting D Sc i hi r
  refine class_whole (k := k) (f := hObj D Sc sy hc (List.replicate r i)) _ _ _
    (fun j => evenShift r j * sy.d i) (fun _ => 0)
    (fun j => (evenSigma D Sc i hi r j : hObj D Sc sy hc (List.replicate r i) ⟶ _))
    (fun j => evenLam D Sc i hi r j) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    have h := evenSigma_mem D Sc i hi (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy) r j
    rw [smul_eq_mul] at h
    exact h
  · intro j
    have h := evenSigma_mem D Sc i hi (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi) r j
    rw [smul_zero] at h
    exact h
  · intro j
    have h := evenLam_mem D Sc i hi (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy) r j
    rw [smul_eq_mul, neg_mul] at h
    exact h
  · intro j
    have h := evenLam_mem D Sc i hi (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi) r j
    rw [smul_zero] at h
    exact h
  · exact S.sum_eq
  · intro j l
    have h := S.orth l j
    change evenLam D Sc i hi r l * evenSigma D Sc i hi r j = _ at h
    change evenLam D Sc i hi r l * evenSigma D Sc i hi r j = _
    rw [h]
    by_cases hjl : j = l
    · subst hjl; rw [ite_eq_left rfl]
    · rw [ite_eq_right (Ne.symm hjl), ite_eq_right hjl]
  · exact fun j => S.sigma_mul j
  · exact fun j => S.mul_lam j

/-- **BE2 Lemma 11.1, even colour, in `K₀(Ḣ_{q,π})`**: `[iʳ] = [r]^!_{q_i} [P(i^{(r)})]`. -/
theorem class_word_even :
    letI := K₀.moduleLaurentInt k (HKar D Sc sy hc)
    K₀.mk (word D Sc sy hc (List.replicate r i)) =
      QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r •
        K₀.mk (dividedPowerEven D Sc sy hc i hi r) := by
  let := K₀.moduleLaurentInt k (HKar D Sc sy hc)
  rw [class_word_summands_even D Sc sy hc i hi r, ← sum_T_evenShift_mul_sub, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [class_raw_shift_int]
  congr 2
  ring

/-- With the unshifted summand the factorial is not balanced:
`[iʳ] = q_i^{r(r-1)/2} [r]^!_{q_i} [(iʳ, 1_{i^{(r)}})]`. -/
theorem class_word_even_unshifted :
    letI := K₀.moduleLaurentInt k (HKar D Sc sy hc)
    K₀.mk (word D Sc sy hc (List.replicate r i)) =
      (T ((r.choose 2 : ℤ) * sy.d i) *
        QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r) •
        K₀.mk (evenSummand D Sc sy hc i hi r 0) := by
  let := K₀.moduleLaurentInt k (HKar D Sc sy hc)
  rw [class_word_summands_even D Sc sy hc i hi r, ← sum_T_evenShift_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [class_raw_shift_int, zero_add]

end Even

/-! ### Odd colours -/

section Odd

variable (i : I) (hi : D.parity i = 1) (n : ℕ)

theorem oddCornerProjector_degree :
    (oddCornerProjector D Sc i hi (n + 2) :
      hObj D Sc sy hc (List.replicate (n + 2) i) ⟶ hObj D Sc sy hc (List.replicate (n + 2) i)) ∈
      degree (R := k) (C := HGr D Sc sy hc) _ _ 0 := by
  have h := oddNilHecke_mem_integerDegree D Sc sy i hi (oppositeProjector_degree n)
  rw [mul_zero] at h
  exact h

theorem oddCornerProjector_even :
    (oddCornerProjector D Sc i hi (n + 2) :
      hObj D Sc sy hc (List.replicate (n + 2) i) ⟶ hObj D Sc sy hc (List.replicate (n + 2) i)) ∈
      Supercategory.parity (R := k) (C := HGr D Sc sy hc) _ _ 0 := by
  have h := oddNilHecke_mem_parity D Sc i hi (oppositeProjector_degree n)
  rw [Int.cast_zero] at h
  exact h

/-- The summand `Q^m Π^p (i^{n+2}, 1_{i^{(n+2)}})` of `Ḣ_{q,π}`. -/
abbrev oddSummandH (m : ℤ) (p : ZMod 2) : HKar D Sc sy hc :=
  raw (f := hObj D Sc sy hc (List.replicate (n + 2) i))
    (oddCornerProjector_idempotent D Sc i hi (n + 2))
    (oddCornerProjector_degree D Sc sy hc i hi n) (oddCornerProjector_even D Sc sy hc i hi n) m p

/-- **BE2 (11.3), odd colour.** The divided power `P(i^{(n+2)})` in `Ḣ_{q,π}`. -/
abbrev dividedPowerOdd : HKar D Sc sy hc :=
  oddSummandH D Sc sy hc i hi n (((n + 2).choose 2 : ℤ) * sy.d i) ((n + 2).choose 2 : ℕ)

/-- The splitting of Lemma 11.1 in `Ḣ_{q,π}`, odd colour. -/
theorem class_word_summands_odd :
    K₀.mk (word D Sc sy hc (List.replicate (n + 2) i)) =
      ∑ ℓ : Sq (n + 2), K₀.mk (oddSummandH D Sc sy hc i hi n (2 * sy.d i * shift n ℓ)
        (shift n ℓ : ZMod 2)) := by
  let S := oddCornerSplitting D Sc i hi n
  refine class_whole (k := k) (f := hObj D Sc sy hc (List.replicate (n + 2) i)) _ _ _
    (fun ℓ => 2 * sy.d i * shift n ℓ) (fun ℓ => (shift n ℓ : ZMod 2))
    (fun ℓ => (S.σ ℓ : hObj D Sc sy hc (List.replicate (n + 2) i) ⟶ _))
    (fun ℓ => S.lam ℓ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun ℓ => oddNilHecke_mem_integerDegree D Sc sy i hi (sigma_degree n ℓ)
  · exact fun ℓ => oddNilHecke_mem_parity D Sc i hi (sigma_degree n ℓ)
  · intro ℓ
    have h := oddNilHecke_mem_integerDegree D Sc sy i hi (lam_degree n ℓ)
    rw [mul_neg] at h
    exact h
  · intro ℓ
    have h := oddNilHecke_mem_parity D Sc i hi (lam_degree n ℓ)
    rw [Int.cast_neg, ZMod.neg_eq_self_mod_two] at h
    exact h
  · exact S.sum_eq
  · intro j l
    have h := S.orth l j
    change S.lam l * S.σ j = _
    rw [h]
    by_cases hjl : j = l
    · subst hjl; rw [ite_eq_left rfl, ite_eq_left rfl]; rfl
    · rw [ite_eq_right (Ne.symm hjl), ite_eq_right hjl]
  · exact fun j => S.sigma_mul j
  · exact fun j => S.mul_lam j

theorem class_oddSummandH (m : ℤ) (s : ℕ) :
    letI := K₀.moduleLaurent k (HKar D Sc sy hc)
    K₀.mk (oddSummandH D Sc sy hc i hi n m (s : ZMod 2)) =
      (T m * piLP ^ s) • K₀.mk (oddSummandH D Sc sy hc i hi n 0 0) := by
  let := K₀.moduleLaurent k (HKar D Sc sy hc)
  rw [mul_smul]
  have hp : ∀ s : ℕ, piLP ^ s • K₀.mk (oddSummandH D Sc sy hc i hi n 0 0) =
      K₀.mk (oddSummandH D Sc sy hc i hi n 0 (s : ZMod 2)) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ' piLP s, mul_smul, ih, class_raw_pi, Nat.cast_succ]
  rw [hp, class_raw_shift, zero_add]

/-- **BE2 Lemma 11.1, odd colour, in `K₀(Ḣ_{q,π})`**:
`[i^{n+2}] = [n+2]^!_{q_i,π} [P(i^{(n+2)})]`. -/
theorem class_word_odd :
    letI := K₀.moduleLaurent k (HKar D Sc sy hc)
    K₀.mk (word D Sc sy hc (List.replicate (n + 2) i)) =
      qpFact (qUnitPi (sy.d i)) piLP (n + 2) • K₀.mk (dividedPowerOdd D Sc sy hc i hi n) := by
  let := K₀.moduleLaurent k (HKar D Sc sy hc)
  have hcomm : qpFact (qUnitPi (sy.d i)) piLP (n + 2) *
      (T (((n + 2).choose 2 : ℤ) * sy.d i) * piLP ^ (n + 2).choose 2) =
      T (((n + 2).choose 2 : ℤ) * sy.d i) * piLP ^ (n + 2).choose 2 *
        qpFact (qUnitPi (sy.d i)) piLP (n + 2) := by ring
  rw [dividedPowerOdd, class_oddSummandH, ← mul_smul, hcomm, class_word_summands_odd,
    ← sum_T_oddShift_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← class_oddSummandH, ← complement_eq_shift, Int.toNat_natCast]
  rfl

end Odd

end OddMath.QuiverHecke
