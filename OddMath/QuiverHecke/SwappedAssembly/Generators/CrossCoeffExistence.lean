/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.Cross
import OddMath.SKM.RouquierCoupled
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Existence of the same-colour crossing coefficient

The coefficient `a` of the mixed block of the same-colour crossing in the swapped action,
`docs/Nondegeneracy/SwappedActionAssembly.md` §2 (A6): `a = (y - x)⁻¹` at even colours and
`a = (x - y)(x² - y²)⁻¹` at odd colours, where `x` is the probe dot of the inner letter and `y`
the reservoir dot of the outer letter on the path `(R,P)` of `Eᵢ Eᵢ`.

The two dots supercommute: `x y = (-1)^{p_i} y x`, by super-interchange through the parity
shift (`homMixedInterchange_dot_exchange`). The written proof (§2, after (A6)) uses that `x` is
a unit (F2: the probe dots are units) and `y` is nilpotent (F3: at each fixed reservoir
content the reservoir dot is nilpotent). Under these two inputs, stated pointwise as
`CrossCoeffInputs`, the denominators `y - x` and `x² - y²` are units of the endomorphism ring,
and `crossCoeffOfInputs` satisfies `CrossCoeff.IsInverse`.

`CrossCoeffInputs.of_factor` derives the pointwise inputs from invertibility of every probe
dot and nilpotence of every reservoir dot as 2-morphisms.

## Main results

* `ProbeReservoir.rpPreDot_comp_rpPostDot`: the Koszul exchange of the two dots.
* `ProbeReservoir.crossCoeffOfInputs_isInverse`: the coefficient satisfies its
  characterizing identities.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- The probe dot and the reservoir dot on the path `(R,P)` of `Eᵢ Eᵢ` supercommute:
`x ≫ y = (-1)^{p_i} (y ≫ x)`. -/
theorem rpPreDot_comp_rpPostDot (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t))) :
    P.rpPreDot i t hv Z ≫ P.rpPostDot i t hv Z =
      koszulSign (D.parity i) (D.parity i) • (P.rpPostDot i t hv Z ≫ P.rpPreDot i t hv Z) :=
  homMixedInterchange_dot_exchange (k := k) (P.T.E i _) (P.W.E i (P.muM_postE i hv))
    (homContentShift D i t.1) Z (P.T.dot i _) (P.W.dot i _) (P.T.dot_mem i _)
    (P.W.dot_mem i _)

/-- The inputs of the written proof for the same-colour coefficient, pointwise on the path
`(R,P)`: the probe dot is a unit (F2) and the reservoir dot is nilpotent (F3). -/
structure CrossCoeffInputs : Prop where
  /-- The probe dot on the inner letter is a unit. -/
  preDot_isUnit : ∀ (i : I) t hv Z, IsUnit (P.rpPreDot i t hv Z)
  /-- The reservoir dot on the outer letter is nilpotent. -/
  postDot_isNilpotent : ∀ (i : I) t hv Z, IsNilpotent (P.rpPostDot i t hv Z)

private theorem rp_mul_eq (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t))) :
    P.rpPostDot i t hv Z * P.rpPreDot i t hv Z =
      koszulSign (D.parity i) (D.parity i) • (P.rpPreDot i t hv Z * P.rpPostDot i t hv Z) := by
  simpa only [End.mul_def] using P.rpPreDot_comp_rpPostDot i t hv Z

private theorem commute_of_even (i : I) (hi : D.parity i = 0) (t : Sector I)
    (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t))) :
    Commute (P.rpPostDot i t hv Z) (P.rpPreDot i t hv Z) := by
  have h := P.rp_mul_eq i t hv Z
  rw [hi] at h
  simpa [koszulSign, Commute, SemiconjBy] using h

private theorem anticommute_of_odd (i : I) (hi : D.parity i = 1) (t : Sector I)
    (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t))) :
    P.rpPostDot i t hv Z * P.rpPreDot i t hv Z =
      -(P.rpPreDot i t hv Z * P.rpPostDot i t hv Z) := by
  have h := P.rp_mul_eq i t hv Z
  rw [hi] at h
  simpa [koszulSign] using h

/-- In a ring, if `y x = -(x y)` then `x` commutes with `y²` and `y` commutes with `x²`. -/
private theorem commute_sq_of_anticommute {R : Type*} [Ring R] {x y : R}
    (h : y * x = -(x * y)) : Commute x (y * y) ∧ Commute y (x * x) := by
  constructor
  · have h' : x * y = -(y * x) := by rw [h, neg_neg]
    show x * (y * y) = y * y * x
    rw [← mul_assoc, h', neg_mul, mul_assoc, h', mul_neg, neg_neg, ← mul_assoc]
  · show y * (x * x) = x * x * y
    rw [← mul_assoc, h, neg_mul, mul_assoc, h, mul_neg, neg_neg, ← mul_assoc]

private theorem parity_eq_one {p : ZMod 2} (hp : p ≠ 0) : p = 1 := by
  fin_cases p
  · exact absurd rfl hp
  · rfl

/-- The denominator of the coefficient, as a unit of the endomorphism ring: `y - x` at even
colours and `x² - y²` at odd colours. -/
def crossDenom (h : P.CrossCoeffInputs) (i : I) (t : Sector I)
    (hv : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t))) :
    (End (P.rpObj i i t hv Z))ˣ :=
  if hi : D.parity i = 0 then
    ((h.postDot_isNilpotent i t hv Z).isUnit_add_left_of_commute
      (h.preDot_isUnit i t hv Z).neg
      ((P.commute_of_even i hi t hv Z).neg_right)).unit
  else
    (((h.postDot_isNilpotent i t hv Z).pow_of_pos two_ne_zero).neg.isUnit_add_left_of_commute
      ((h.preDot_isUnit i t hv Z).pow 2)
      (by
        have hc := commute_sq_of_anticommute (P.anticommute_of_odd i
          (parity_eq_one hi) t hv Z)
        simpa [pow_two] using ((hc.2.symm.mul_right hc.2.symm).symm).neg_left)).unit

/-- The same-colour crossing coefficient: `(y - x)⁻¹` at even colours and
`(x - y)(x² - y²)⁻¹` at odd colours. -/
def crossCoeffOfInputs (h : P.CrossCoeffInputs) : P.CrossCoeff Sc where
  a i t hv Z :=
    if D.parity i = 0 then ((P.crossDenom h i t hv Z)⁻¹ : (End (P.rpObj i i t hv Z))ˣ)
    else ((P.crossDenom h i t hv Z)⁻¹ : (End (P.rpObj i i t hv Z))ˣ) *
      (P.rpPreDot i t hv Z - P.rpPostDot i t hv Z)

theorem crossCoeffOfInputs_isInverse (h : P.CrossCoeffInputs) :
    (P.crossCoeffOfInputs h).IsInverse := by
  constructor
  · intro i hi t hv Z
    have hd : ((P.crossDenom h i t hv Z : (End (P.rpObj i i t hv Z))ˣ) :
        End (P.rpObj i i t hv Z)) = P.rpPostDot i t hv Z - P.rpPreDot i t hv Z := by
      simp [crossDenom, hi, sub_eq_add_neg, add_comm]
    simp only [crossCoeffOfInputs, hi, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [← End.mul_def, ← hd, Units.mul_inv]; rfl
    · rw [← End.mul_def, ← hd, Units.inv_mul]; rfl
  · intro i hi t hv Z
    have hi0 : D.parity i ≠ 0 := by rw [hi]; decide
    simp only [crossCoeffOfInputs, hi0, ↓reduceIte]
    have hc := commute_sq_of_anticommute (P.anticommute_of_odd i hi t hv Z)
    set x := P.rpPreDot i t hv Z
    set y := P.rpPostDot i t hv Z
    have hd : ((P.crossDenom h i t hv Z : (End (P.rpObj i i t hv Z))ˣ) :
        End (P.rpObj i i t hv Z)) = x * x - y * y := by
      simp [crossDenom, hi0, sub_eq_add_neg, add_comm, pow_two, x, y]
    -- `x - y` commutes with the denominator.
    have hcomm : Commute (x - y) (x * x - y * y) := by
      refine (Commute.sub_left ?_ ?_)
      · exact ((Commute.refl x).mul_right (Commute.refl x)).sub_right hc.1
      · exact (hc.2.sub_right ((Commute.refl y).mul_right (Commute.refl y)))
    rw [← hd] at hcomm
    have hxx : x ≫ x - y ≫ y = x * x - y * y := by
      simp only [End.mul_def]
    rw [hxx]
    refine ⟨?_, ?_⟩
    · rw [← End.mul_def, ← hd, ← mul_assoc, Units.mul_inv, one_mul]
    · rw [← End.mul_def, ← hd, mul_assoc, hcomm.eq, ← mul_assoc, Units.inv_mul, one_mul]

/-- The pointwise inputs follow from invertibility of every probe dot and nilpotence of every
reservoir dot as 2-morphisms (F2, F3). -/
theorem CrossCoeffInputs.of_factor
    (hT : ∀ (i : I) {x y : X} (h : x + D.α i = y), IsUnit (show End (P.T.E i h) from P.T.dot i h))
    (hW : ∀ (i : I) {x y : X} (h : x + D.α i = y),
      IsNilpotent (show End (P.W.E i h) from P.W.dot i h)) :
    P.CrossCoeffInputs := by
  constructor
  · intro i t hv Z
    exact ((hT i (P.muP_preE i (nextSector (true, i) false t))).map
      ((homPost (k := k) Z).mapEnd _)).map ((P.step (true, i) false t hv).mapEnd _)
  · intro i t hv Z
    obtain ⟨n, hn⟩ := hW i (P.muM_postE i hv)
    refine ⟨n, ?_⟩
    have := homContentPostDot_power (k := k) P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) n
      ((P.step (true, i) true _ trivial).obj Z)
    simp only [rpPostDot]
    rw [this, rouquierPower_eq_pow, hn]
    have hz : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), f ◁ (0 : g ⟶ g) = 0 := fun f g =>
      (homPre (k := k) f).map_zero g g
    rw [hz, Functor.map_zero]

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
