/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Instances.Rat
import OddMath.SKM.LaurentianHoms
import OddMath.SKM.SymComponentBasis

/-!
# The product formula for the graded superdimension of `SYM`

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 12.1, equation
(dum): the factor `S` is the graded superdimension of the coefficient algebra `SYM`, and as a
formal power series it is the product, over the generators of `SYM`, of
`(1 - q^{deg e_{i,r}})⁻¹` for the even generators `e_{i,r}` and `1 + π q^{2 d_i}` for the odd
generators `δ_i` (`i` odd); the corrected form of the printed product is ERRATA [BE2] 8.

The product is infinite in general (infinitely many `e_{i,r}`, possibly infinitely many
colours). It is stated as `HasProd` in `PowerSeries ℚ` with the coefficientwise topology
(`PowerSeries.WithPiTopology`), with `π` evaluated at `σ`, `σ² = 1`. The hypothesis
`sy.DegreeLocallyFinite` (finitely many colours below each degree) makes each coefficient a
finite product; it holds for finitely many colours.

## Main results

* `MonomialSeries.hasProd_mk_of_locallyFinite`: a product of power series `∑ₖ aₙ(k) X^k` with
  `aₙ(0) = 1`, vanishing in degrees `0 < k < deg n`, converges when only finitely many indices
  have degree at most each `N`.
* `MonomialSeries.hasProd_monomialSeries`: for even generators of degrees `dE` and odd
  generators of degrees `dO`, the product of the factors `(1 - X^{dE e})⁻¹`
  (`MonomialSeries.geomSeries`) and `1 + σ X^{dO o}` is the generating function of the monomials
  `(E →₀ ℕ) × Finset O`, counted with sign `σ^{#odd factors}`.
* `SKM.hasProd_symFactor`, `SKM.symDimension_eq_tprod`: the graded superdimension
  `symDimension` of `SYM` is `∏' g, symFactor sy σ g`.
-/

noncomputable section

open PowerSeries Finset Filter
open scoped PowerSeries.WithPiTopology

namespace OddMath.SKM.MonomialSeries

section Convergence
variable {G R : Type*} [CommRing R] [TopologicalSpace R]

/-- A product of power series `∑ₖ a g k X^k` with constant term `1`, whose coefficients vanish
in degrees `0 < k < deg g`, converges coefficientwise when only finitely many `g` have
`deg g ≤ n` for each `n`; the coefficient of `X^n` of the product is a finite sum. -/
theorem hasProd_mk_of_locallyFinite [DecidableEq G] (a : G → ℕ → R) (deg : G → ℕ)
    (hfin : ∀ n, {g | deg g ≤ n}.Finite) (h0 : ∀ g, a g 0 = 1)
    (hlow : ∀ g k, 0 < k → k < deg g → a g k = 0) :
    HasProd (fun g => PowerSeries.mk (a g))
      (PowerSeries.mk fun n => ∑ l ∈ (hfin n).toFinset.finsuppAntidiag n,
        ∏ g ∈ (hfin n).toFinset, a g (l g)) := by
  rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  set S := (hfin n).toFinset with hS
  refine tendsto_const_nhds.congr' ?_
  show ∀ᶠ s in atTop, _
  rw [eventually_atTop]
  refine ⟨S, fun s hs => ?_⟩
  dsimp only
  rw [coeff_prod]
  simp only [coeff_mk]
  have hsub : S.finsuppAntidiag n ⊆ s.finsuppAntidiag n := by
    intro l hl
    rw [mem_finsuppAntidiag] at hl ⊢
    refine ⟨?_, hl.2.trans hs⟩
    rw [← hl.1]
    exact (Finset.sum_subset hs fun g _ hg => by
      have : g ∉ l.support := fun h => hg (hl.2 h)
      simpa using this).symm
  symm
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [mem_finsuppAntidiag] at hl
    symm
    apply Finset.prod_subset hs
    intro g _ hg
    have : g ∉ l.support := fun h => hg (hl.2 h)
    rw [Finsupp.notMem_support_iff.mp this, h0]
  · intro l hl hl'
    rw [mem_finsuppAntidiag] at hl hl'
    have : ¬ l.support ⊆ S := fun h => hl' ⟨by
      rw [← hl.1]; exact Finset.sum_subset hs fun g _ hg => by
        have : g ∉ l.support := fun h' => hg (h h')
        simpa using this, h⟩
    obtain ⟨g, hgl, hgS⟩ := Finset.not_subset.mp this
    apply Finset.prod_eq_zero (hl.2 hgl)
    apply hlow
    · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hgl)
    · have hle : l g ≤ n := by
        rw [← hl.1]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hl.2 hgl)
      by_contra h
      apply hgS
      simp only [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      omega

end Convergence

section Monomials
variable {E O : Type*} (dE : E → ℕ) (dO : O → ℕ)

/-- The weight of a monomial `∏ eₓ^{η.1 x} ∏_{o ∈ η.2} o`: even generators have degrees
`dE`, odd generators (which occur at most once) have degrees `dO`. -/
def monomialWeight (η : (E →₀ ℕ) × Finset O) : ℕ :=
  (η.1.sum fun e m => m * dE e) + ∑ o ∈ η.2, dO o

section Bij
variable {R : Type*} [Field R]

/-- The monomial of an exponent function on `E ⊕ O` whose values are multiples of the degrees
(the even part divided by the degrees, the odd part its support). -/
def toMonomial (l : (E ⊕ O) →₀ ℕ) : (E →₀ ℕ) × Finset O :=
  (Finsupp.onFinset l.support.toLeft (fun e => l (Sum.inl e) / dE e) (by
    intro e h
    rw [mem_toLeft, Finsupp.mem_support_iff]
    intro h'
    apply h
    simp [h']), l.support.toRight)

open Classical in
/-- The exponent function of a monomial: `η.1 e * dE e` at `e`, `dO o` at `o ∈ η.2`. -/
def ofMonomial (η : (E →₀ ℕ) × Finset O) : (E ⊕ O) →₀ ℕ :=
  Finsupp.onFinset (η.1.support.disjSum η.2)
    (Sum.elim (fun e => η.1 e * dE e) (fun o => if o ∈ η.2 then dO o else 0)) (by
    rintro (e | o) h
    · simp only [Sum.elim_inl] at h
      simp only [inl_mem_disjSum, Finsupp.mem_support_iff]
      intro h'; apply h; simp [h']
    · simp only [Sum.elim_inr] at h
      simp only [inr_mem_disjSum]
      by_contra h'; apply h; simp [h'])

theorem ofMonomial_inl (η : (E →₀ ℕ) × Finset O) (e : E) :
    ofMonomial dE dO η (Sum.inl e) = η.1 e * dE e := by
  simp [ofMonomial]

open Classical in
theorem ofMonomial_inr (η : (E →₀ ℕ) × Finset O) (o : O) :
    ofMonomial dE dO η (Sum.inr o) = if o ∈ η.2 then dO o else 0 := by
  simp [ofMonomial]

theorem toMonomial_ofMonomial (hE : ∀ e, 0 < dE e) (hO : ∀ o, 0 < dO o)
    (η : (E →₀ ℕ) × Finset O) : toMonomial dE (ofMonomial dE dO η) = η := by
  classical
  ext e
  · simp [toMonomial, ofMonomial_inl, Nat.mul_div_cancel _ (hE e)]
  · simp only [toMonomial, mem_toRight, Finsupp.mem_support_iff, ofMonomial_inr]
    have := hO e
    split_ifs with h <;> simp [h]; omega

theorem sum_ofMonomial (η : (E →₀ ℕ) × Finset O) :
    ((ofMonomial dE dO η).sum fun _ m => m) = monomialWeight dE dO η := by
  classical
  rw [ofMonomial, Finsupp.onFinset_sum _ (fun _ => rfl), sum_disjSum]
  simp only [Sum.elim_inl, Sum.elim_inr, monomialWeight, Finsupp.sum]
  congr 1
  exact Finset.sum_congr rfl fun o ho => by simp [ho]


/-- The coefficient sequences of the factors: `[dE e ∣ k]` for an even generator, and
`1, σ` in degrees `0, dO o` for an odd generator. -/
def factorCoeff (σ : R) : E ⊕ O → ℕ → R :=
  Sum.elim (fun e k => if dE e ∣ k then 1 else 0)
    (fun o k => if k = 0 then 1 else if k = dO o then σ else 0)

theorem factorCoeff_inl_ne_zero {σ : R} {e : E} {k : ℕ}
    (h : factorCoeff dE dO σ (Sum.inl e) k ≠ 0) : dE e ∣ k := by
  by_contra h'
  simp [factorCoeff, h'] at h

theorem factorCoeff_inr_ne_zero {σ : R} {o : O} {k : ℕ}
    (h : factorCoeff dE dO σ (Sum.inr o) k ≠ 0) : k = 0 ∨ k = dO o := by
  by_contra h'
  simp only [not_or] at h'
  simp [factorCoeff, h'.1, h'.2] at h

theorem ofMonomial_toMonomial (σ : R) (S : Finset (E ⊕ O)) (l : (E ⊕ O) →₀ ℕ)
    (hl : l.support ⊆ S) (hv : ∀ g ∈ S, factorCoeff dE dO σ g (l g) ≠ 0) :
    ofMonomial dE dO (toMonomial dE l) = l := by
  classical
  ext (e | o)
  · rw [ofMonomial_inl]
    simp only [toMonomial, Finsupp.onFinset_apply]
    by_cases h : l (Sum.inl e) = 0
    · simp [h]
    · exact Nat.div_mul_cancel
        (factorCoeff_inl_ne_zero dE dO (hv _ (hl (Finsupp.mem_support_iff.mpr h))))
  · rw [ofMonomial_inr]
    simp only [toMonomial, mem_toRight, Finsupp.mem_support_iff]
    by_cases h : l (Sum.inr o) = 0
    · simp [h]
    · have := (factorCoeff_inr_ne_zero dE dO
        (hv _ (hl (Finsupp.mem_support_iff.mpr h)))).resolve_left h
      rw [this] at h ⊢
      simp [h]

theorem prod_factorCoeff (σ : R) (S : Finset (E ⊕ O)) (l : (E ⊕ O) →₀ ℕ)
    (hl : l.support ⊆ S) (hv : ∀ g ∈ S, factorCoeff dE dO σ g (l g) ≠ 0) :
    ∏ g ∈ S, factorCoeff dE dO σ g (l g) = σ ^ (toMonomial dE l).2.card := by
  classical
  rw [← toLeft_disjSum_toRight (u := S), prod_disjSum]
  have h1 : ∏ e ∈ S.toLeft, factorCoeff dE dO σ (Sum.inl e) (l (Sum.inl e)) = 1 := by
    apply Finset.prod_eq_one
    intro e he
    have := factorCoeff_inl_ne_zero dE dO (hv _ (mem_toLeft.mp he))
    simp [factorCoeff, this]
  have h2 : ∀ o ∈ S.toRight, factorCoeff dE dO σ (Sum.inr o) (l (Sum.inr o)) =
      if o ∈ l.support.toRight then σ else 1 := by
    intro o ho
    simp only [mem_toRight, Finsupp.mem_support_iff]
    by_cases h : l (Sum.inr o) = 0
    · simp [factorCoeff, h]
    · have := (factorCoeff_inr_ne_zero dE dO (hv _ (mem_toRight.mp ho))).resolve_left h
      simp [factorCoeff, this]
  rw [h1, one_mul, Finset.prod_congr rfl h2, Finset.prod_ite_mem, Finset.prod_const]
  congr 2
  apply Finset.inter_eq_right.mpr
  intro o ho
  exact mem_toRight.mpr (hl (mem_toRight.mp ho))


theorem le_ofMonomial (η : (E →₀ ℕ) × Finset O) (g : E ⊕ O)
    (hg : ofMonomial dE dO η g ≠ 0) : Sum.elim dE dO g ≤ ofMonomial dE dO η g := by
  classical
  rcases g with e | o
  · rw [ofMonomial_inl] at hg ⊢
    have : 0 < η.1 e := Nat.pos_of_ne_zero fun h => hg (by simp [h])
    simpa using Nat.le_mul_of_pos_left (dE e) this
  · rw [ofMonomial_inr] at hg ⊢
    split_ifs with h
    · simp
    · simp [h] at hg

/-- The coefficient of the product of the factors over the generators of degree at most `n`
counts the monomials of weight `n`, with sign `σ^{#odd factors}`. -/
theorem sum_finsuppAntidiag_factorCoeff [DecidableEq (E ⊕ O)] (hE : ∀ e, 0 < dE e)
    (hO : ∀ o, 0 < dO o)
    (σ : R) (hσ : σ ^ 2 = 1) (n : ℕ) (S : Finset (E ⊕ O))
    (hS : ∀ g, g ∈ S ↔ Sum.elim dE dO g ≤ n) :
    ∑ l ∈ S.finsuppAntidiag n, ∏ g ∈ S, factorCoeff dE dO σ g (l g) =
      ∑ p : ZMod 2, σ ^ p.val *
        (Nat.card {η // monomialWeight dE dO η = n ∧ (η.2.card : ZMod 2) = p} : R) := by
  classical
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  let f : ((E ⊕ O) →₀ ℕ) → R := fun l => ∏ g ∈ S, factorCoeff dE dO σ g (l g)
  let A := S.finsuppAntidiag n
  let V := A.filter (fun l => f l ≠ 0)
  have hV : ∀ l ∈ V, l.support ⊆ S ∧ ∀ g ∈ S, factorCoeff dE dO σ g (l g) ≠ 0 := by
    intro l hl
    rw [mem_filter, mem_finsuppAntidiag] at hl
    exact ⟨hl.1.2, Finset.prod_ne_zero_iff.mp hl.2⟩
  have hinj : Set.InjOn (toMonomial (O := O) dE) (V : Set ((E ⊕ O) →₀ ℕ)) := by
    intro l₁ h₁ l₂ h₂ heq
    rw [← ofMonomial_toMonomial dE dO σ S l₁ (hV l₁ h₁).1 (hV l₁ h₁).2,
      ← ofMonomial_toMonomial dE dO σ S l₂ (hV l₂ h₂).1 (hV l₂ h₂).2, heq]
  let B := V.image (toMonomial dE)
  have hB : ∀ η, η ∈ B ↔ monomialWeight dE dO η = n := by
    intro η
    constructor
    · intro h
      obtain ⟨l, hl, rfl⟩ := mem_image.mp h
      rw [← sum_ofMonomial, ofMonomial_toMonomial dE dO σ S l (hV l hl).1 (hV l hl).2,
        Finsupp.sum_of_support_subset _ (hV l hl).1 _ (fun _ _ => rfl)]
      exact (mem_finsuppAntidiag.mp (mem_filter.mp hl).1).1
    · intro h
      refine mem_image.mpr ⟨ofMonomial dE dO η, ?_, toMonomial_ofMonomial dE dO hE hO η⟩
      have hsupp : (ofMonomial dE dO η).support ⊆ S := by
        intro g hg
        rw [hS]
        refine (le_ofMonomial dE dO η g (Finsupp.mem_support_iff.mp hg)).trans ?_
        rw [← h, ← sum_ofMonomial]
        exact Finset.single_le_sum (f := fun x => ofMonomial dE dO η x)
          (fun _ _ => Nat.zero_le _) hg
      refine mem_filter.mpr ⟨mem_finsuppAntidiag.mpr ⟨?_, hsupp⟩, ?_⟩
      · rw [← h, ← sum_ofMonomial, Finsupp.sum_of_support_subset _ hsupp _ (fun _ _ => rfl)]
      · refine Finset.prod_ne_zero_iff.mpr fun g _ => ?_
        rcases g with e | o
        · simp [factorCoeff, ofMonomial_inl]
        · rw [ofMonomial_inr]
          split_ifs
          · simp only [factorCoeff, Sum.elim_inr]
            split_ifs <;> simp [hσ0]
          · simp [factorCoeff]
  calc ∑ l ∈ A, f l = ∑ l ∈ V, f l := (sum_filter_ne_zero A).symm
    _ = ∑ l ∈ V, σ ^ (toMonomial dE l).2.card :=
        Finset.sum_congr rfl fun l hl => prod_factorCoeff dE dO σ S l (hV l hl).1 (hV l hl).2
    _ = ∑ η ∈ B, σ ^ η.2.card :=
        (Finset.sum_image (f := fun η : (E →₀ ℕ) × Finset O => σ ^ η.2.card) hinj).symm
    _ = ∑ p : ZMod 2, ∑ η ∈ B with (η.2.card : ZMod 2) = p, σ ^ η.2.card :=
        (sum_fiberwise B (fun η => (η.2.card : ZMod 2)) _).symm
    _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_congr rfl (g := fun _ => σ ^ p.val), sum_const, nsmul_eq_mul, mul_comm]
        · congr 2
          rw [← Nat.card_eq_finsetCard]
          exact Nat.card_congr (Equiv.subtypeEquivRight fun η => by
            rw [mem_filter, hB])
        · intro η hη
          rw [← (mem_filter.mp hη).2, ZMod.val_natCast, ← pow_eq_pow_mod _ hσ]

/-- The geometric series `∑ₘ X^{dm}`, the inverse of `1 - X^d`
(`one_sub_X_pow_mul_geomSeries`). -/
def geomSeries (d : ℕ) : PowerSeries R := PowerSeries.mk fun n => if d ∣ n then 1 else 0

/-- The geometric series is the inverse of `1 - X^d`. -/
theorem one_sub_X_pow_mul_geomSeries {d : ℕ} (hd : 0 < d) :
    (1 - X ^ d) * geomSeries (R := R) d = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', geomSeries, coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.not_le.mpr hd]
  · by_cases hdn : d ≤ n
    · by_cases h : d ∣ n
      · simp [hn.ne', hdn, h, Nat.dvd_sub_self_right]
      · have hlt : d < n := lt_of_le_of_ne hdn (by rintro rfl; exact h dvd_rfl)
        simp [hn.ne', hdn, h, Nat.dvd_sub_self_right, hlt]
    · have : ¬ d ∣ n := Nat.not_dvd_of_pos_of_lt hn (by omega)
      simp [hn.ne', hdn, this]

/-- Generating function of the monomials `(E →₀ ℕ) × Finset O`, graded by weight, with the
parity of the number of odd factors evaluated at `σ`. -/
def monomialSeries (σ : R) : PowerSeries R :=
  PowerSeries.mk fun n => ∑ p : ZMod 2, σ ^ p.val *
    (Nat.card {η // monomialWeight dE dO η = n ∧ (η.2.card : ZMod 2) = p} : R)

/-- **Product formula for monomial generating functions.** The product of `(1 - X^{dE e})⁻¹`
over the even generators and `1 + σ X^{dO o}` over the odd generators is the generating
function of the monomials, counted with sign `σ^{#odd factors}`. -/
theorem hasProd_monomialSeries [TopologicalSpace R] (hE : ∀ e, 0 < dE e) (hO : ∀ o, 0 < dO o)
    (hfin : ∀ n, {g : E ⊕ O | Sum.elim dE dO g ≤ n}.Finite) (σ : R) (hσ : σ ^ 2 = 1) :
    HasProd (Sum.elim (fun e => geomSeries (dE e)) (fun o => 1 + PowerSeries.C σ * X ^ dO o))
      (monomialSeries dE dO σ) := by
  classical
  have hfac : Sum.elim (fun e => geomSeries (R := R) (dE e))
      (fun o => 1 + PowerSeries.C σ * X ^ dO o) =
      fun g => PowerSeries.mk (factorCoeff dE dO σ g) := by
    funext g
    rcases g with e | o
    · rfl
    · ext k
      have hpos := (hO o).ne'
      simp only [Sum.elim_inr, map_add, coeff_one, coeff_C_mul, coeff_X_pow, coeff_mk,
        factorCoeff]
      split_ifs <;> simp_all
  have h0 : ∀ g, factorCoeff dE dO σ g 0 = 1 := by
    rintro (e | o) <;> simp [factorCoeff]
  have hlow : ∀ g k, 0 < k → k < Sum.elim dE dO g → factorCoeff dE dO σ g k = 0 := by
    rintro (e | o) k hk hlt
    · simp only [factorCoeff, Sum.elim_inl, ite_eq_right_iff]
      exact fun h => absurd h (Nat.not_dvd_of_pos_of_lt hk hlt)
    · simp only [Sum.elim_inr] at hlt
      simp [factorCoeff, hk.ne', hlt.ne]
  rw [hfac]
  convert hasProd_mk_of_locallyFinite (factorCoeff dE dO σ) (Sum.elim dE dO) hfin h0 hlow using 1
  ext n
  rw [monomialSeries, coeff_mk, coeff_mk, sum_finsuppAntidiag_factorCoeff dE dO hE hO σ hσ n
    (hfin n).toFinset (fun g => by simp)]

/-- A Laurent series with no negative coefficients is the image of the power series of its
nonnegative coefficients. -/
theorem coe_mk_coeff (L : LaurentSeries R) (h : ∀ n < 0, L.coeff n = 0) :
    ((PowerSeries.mk fun n : ℕ => L.coeff n : PowerSeries R) : LaurentSeries R) = L := by
  ext n
  rw [PowerSeries.coeff_coe]
  split_ifs with hn
  · exact (h n hn).symm
  · rw [coeff_mk, Int.natAbs_of_nonneg (not_lt.mp hn)]

end Bij
end Monomials
end OddMath.SKM.MonomialSeries

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} (sy : Symmetrizer D)

/-- The factor of the product formula at a generator of `SYM`: `(1 - q^{deg e_{i,r}})⁻¹` at an
even generator `e_{i,r}` and `1 + σ q^{2 d_i}` at an odd generator `δ_i`. -/
def symFactor (σ : ℚ) : SYMGen D → PowerSeries ℚ :=
  Sum.elim (fun a => MonomialSeries.geomSeries (symGenNatDegree D sy (Sum.inl a)))
    (fun i => 1 + PowerSeries.C σ * PowerSeries.X ^ symGenNatDegree D sy (Sum.inr i))

/-- The even factor is the inverse of `1 - q^{deg e_{i,r}}`. -/
theorem one_sub_X_pow_mul_symFactor_inl (σ : ℚ) (a : I × ℕ) :
    (1 - PowerSeries.X ^ symGenNatDegree D sy (Sum.inl a)) * symFactor sy σ (Sum.inl a) = 1 :=
  MonomialSeries.one_sub_X_pow_mul_geomSeries (symGenNatDegree_pos sy _)

/-- `symDimension` as a power series: its coefficients in nonnegative degrees. -/
def symPowerSeries (k : Type w) [Field k] (σ : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (symDimension sy k σ).coeff n

theorem coe_symPowerSeries (k : Type w) [Field k] (σ : ℚ) :
    ((symPowerSeries sy k σ : PowerSeries ℚ) : LaurentSeries ℚ) = symDimension sy k σ :=
  MonomialSeries.coe_mk_coeff _ (symDimension_coeff_neg sy k σ)

theorem coefficientBidegree_fst (η : SYM.CoefficientIndex D) :
    (SYM.coefficientBidegree sy η).1 =
      (MonomialSeries.monomialWeight (fun a => symGenNatDegree D sy (Sum.inl a))
        (fun i => symGenNatDegree D sy (Sum.inr i)) η : ℤ) := by
  simp only [SYM.coefficientBidegree, MonomialSeries.monomialWeight, Finsupp.sum,
    Nat.cast_add, Nat.cast_sum, Nat.cast_mul, symGenNatDegree_cast]

/-- **Product formula for `SYM`** (BE2 Theorem 12.1, the factor `S` of (dum), in the corrected
form of ERRATA [BE2] 8): with `π ↦ σ`, `σ² = 1`, the graded superdimension of `SYM` is the
coefficientwise convergent product of `(1 - q^{deg e_{i,r}})⁻¹` over the even generators and
`1 + σ q^{2 d_i}` over the odd generators `δ_i`. -/
theorem hasProd_symFactor (k : Type w) [Field k] (hf : sy.DegreeLocallyFinite) (σ : ℚ)
    (hσ : σ ^ 2 = 1) : HasProd (symFactor sy σ) (symPowerSeries sy k σ) := by
  have h := MonomialSeries.hasProd_monomialSeries (R := ℚ)
    (fun a => symGenNatDegree D sy (Sum.inl a)) (fun i => symGenNatDegree D sy (Sum.inr i))
    (fun _ => symGenNatDegree_pos sy _) (fun _ => symGenNatDegree_pos sy _)
    (fun n => (symGenNatDegree_finite sy hf n).subset (by rintro (a | i) h <;> exact h)) σ hσ
  have he : symPowerSeries sy k σ = MonomialSeries.monomialSeries
      (fun a => symGenNatDegree D sy (Sum.inl a)) (fun i => symGenNatDegree D sy (Sum.inr i))
      σ := by
    ext n
    rw [symPowerSeries, MonomialSeries.monomialSeries, coeff_mk, coeff_mk,
      symDimension_coeff_eq_card]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 2
    exact Nat.card_congr (Equiv.subtypeEquivRight fun η => by
      rw [Prod.ext_iff, coefficientBidegree_fst]
      exact and_congr Nat.cast_inj Iff.rfl)
  rw [he]
  exact h

/-- The graded superdimension of `SYM` as the infinite product of `symFactor`, read in
`LaurentSeries ℚ`. -/
theorem symDimension_eq_tprod (k : Type w) [Field k] (hf : sy.DegreeLocallyFinite) (σ : ℚ)
    (hσ : σ ^ 2 = 1) :
    symDimension sy k σ = ((∏' g, symFactor sy σ g : PowerSeries ℚ) : LaurentSeries ℚ) := by
  rw [(hasProd_symFactor sy k hf σ hσ).tprod_eq, coe_symPowerSeries]

end OddMath.SKM
