import OddMath.SKM.RouquierShiftedAdjunction

/-!
# Leftward cups and caps from the local inverses

This ports the generator definitions of `Categorification/TwoRep/RouqSl2.lean`
(`RouqLoc.sigL`, `cupN`, `capN`, `cupL`, `capL`) and the packaging step of
`RouqAdjunction.lean`/`RouqModel.lean` (`RouqFamily.adjL`) to super Rouquier data.
Its downstream consumer is `homContentPreAdjunction` of
`RouquierShiftedAdjunction.lean`, through `RouquierLeftAdjoints`.

The leftward crossing is minus the `E F → F E` component of the inverse of the
mate; the leftward cup and cap are the extreme dotted inverse components, or the
rightward cup/cap composed with the leftward crossing, exactly as in the even case.
They have parity `|i|(⟨hᵢ, λ⟩ + 1)` (`cupL_mem`, `capL_mem`).

The super analogue of Brundan's Theorem 4.3 (the two zigzag identities) is the
named obligation `RouquierFamily.LeftZigzags`. It is stated up to a unit scalar,
so it does not depend on a sign normalization of the leftward cup or cap: in a
2-supercategory super interchange of the cup with itself forces the `E`-zigzag
to be `(-1)^σ` times the `F`-zigzag whenever the cup is nonzero.
`RouquierFamily.leftAdjointsOfZigzags` turns the obligation into
`RouquierLeftAdjoints`. The obligation itself is not proved here.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

omit [TwoSupercategory k B] in
theorem rouquierPower_mem {a b : B} {E : a ⟶ b} {x : E ⟶ E} {p : ZMod 2}
    (hx : x ∈ parity (R := k) _ _ p) (n : ℕ) :
    rouquierPower x n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul]
    exact id_mem (R := k) E
  | succ n ih =>
    have h := comp_mem ih hx
    rwa [show (n : ZMod 2) * p + p = ((n + 1 : ℕ) : ZMod 2) * p by push_cast; ring] at h

theorem toNat_cast_zmod2 {z : ℤ} (hz : 0 ≤ z) : ((z.toNat : ℕ) : ZMod 2) = (z : ZMod 2) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]

namespace SuperRouquierLoc
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {p : ZMod 2} {h : ℤ}
  (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)

/-- The rightward cap with `n` dots `Fᵢ Eᵢ 1_λ → 1_λ`. -/
def capD (_L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h) (n : ℕ) : F₁ ≫ E₁ ⟶ 𝟙 b :=
  F₁ ◁ rouquierPower x₁ n ≫ A₁.counit

/-- The rightward cup with `n` dots `1_λ → Eᵢ Fᵢ 1_λ`. -/
def cupD (_L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h) (n : ℕ) : 𝟙 b ⟶ E₂ ≫ F₂ :=
  A₂.unit ≫ rouquierPower x₂ n ▷ F₂

/-- The leftward crossing: minus the `E F → F E` component of the inverse of the mate. -/
def sigL : E₂ ≫ F₂ ⟶ F₁ ≫ E₁ :=
  if hh : 0 ≤ h then -(L.invPos hh).f' else -(L.invNeg (le_of_lt (not_le.mp hh))).f'

/-- The dotted leftward cups: the `1 → F E` components of the positive inverse. -/
def cupN (n : ℕ) : 𝟙 b ⟶ F₁ ≫ E₁ := if hh : 0 ≤ h then (L.invPos hh).g' n else 0

/-- The dotted leftward caps: the `E F → 1` components of the negative inverse. -/
def capN (n : ℕ) : E₂ ≫ F₂ ⟶ 𝟙 b := if hh : h ≤ 0 then (L.invNeg hh).g' n else 0

/-- The leftward cup: the last dotted inverse cup if `h > 0`, otherwise the rightward cup
with `-h` dots followed by the leftward crossing. -/
def cupL : 𝟙 b ⟶ F₁ ≫ E₁ :=
  if 0 < h then L.cupN (h - 1).toNat else L.cupD (-h).toNat ≫ L.sigL

/-- The leftward cap: the last dotted inverse cap if `h < 0`, otherwise minus the
leftward crossing followed by the rightward cap with `h` dots. -/
def capL : E₂ ≫ F₂ ⟶ 𝟙 b :=
  if h < 0 then L.capN (-h - 1).toNat else -(L.sigL ≫ L.capD h.toNat)

theorem capD_mem (n : ℕ) : L.capD n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  have hm := comp_mem (TwoSupercategory.whiskerLeft_mem F₁ (rouquierPower_mem L.dot₁_mem n))
    A₁.counit_mem
  rwa [add_zero] at hm

theorem cupD_mem (n : ℕ) : L.cupD n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  have hm := comp_mem A₂.unit_mem
    (TwoSupercategory.whiskerRight_mem F₂ (rouquierPower_mem L.dot₂_mem n))
  rwa [zero_add] at hm

omit [TwoSupercategory k B] in
theorem sigL_mem : L.sigL ∈ parity (R := k) _ _ p := by
  unfold sigL
  split_ifs with hh
  · exact Submodule.neg_mem _ (L.invPos hh).f'_mem
  · exact Submodule.neg_mem _ (L.invNeg _).f'_mem

omit [TwoSupercategory k B] in
theorem cupN_mem (n : ℕ) : L.cupN n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  unfold cupN
  split_ifs with hh
  · exact (L.invPos hh).g'_mem n
  · exact Submodule.zero_mem _

omit [TwoSupercategory k B] in
theorem capN_mem (n : ℕ) : L.capN n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  unfold capN
  split_ifs with hh
  · exact (L.invNeg hh).g'_mem n
  · exact Submodule.zero_mem _

private theorem zmod2_cases (P H : ZMod 2) (Q : ZMod 2 → ZMod 2 → Prop)
    (h00 : Q 0 0) (h01 : Q 0 1) (h10 : Q 1 0) (h11 : Q 1 1) : Q P H := by
  fin_cases P <;> fin_cases H <;> assumption

/-- The leftward cup has parity `p(h + 1)`. -/
theorem cupL_mem : L.cupL ∈ parity (R := k) _ _ (p * ((h : ZMod 2) + 1)) := by
  unfold cupL
  split_ifs with hh
  · have hm := L.cupN_mem (h - 1).toNat
    rw [toNat_cast_zmod2 (by omega)] at hm
    convert hm using 2
    push_cast
    refine zmod2_cases p (h : ZMod 2) (fun P H => P * (H + 1) = (H - 1) * P) ?_ ?_ ?_ ?_ <;>
      decide
  · have hm := comp_mem (L.cupD_mem (-h).toNat) L.sigL_mem
    rw [toNat_cast_zmod2 (by omega)] at hm
    convert hm using 2
    push_cast
    refine zmod2_cases p (h : ZMod 2) (fun P H => P * (H + 1) = -H * P + P) ?_ ?_ ?_ ?_ <;>
      decide

/-- The leftward cap has parity `p(h + 1)`. -/
theorem capL_mem : L.capL ∈ parity (R := k) _ _ (p * ((h : ZMod 2) + 1)) := by
  unfold capL
  split_ifs with hh
  · have hm := L.capN_mem (-h - 1).toNat
    rw [toNat_cast_zmod2 (by omega)] at hm
    convert hm using 2
    push_cast
    refine zmod2_cases p (h : ZMod 2) (fun P H => P * (H + 1) = (-H - 1) * P) ?_ ?_ ?_ ?_ <;>
      decide
  · have hm := comp_mem L.sigL_mem (L.capD_mem h.toNat)
    rw [toNat_cast_zmod2 (by omega)] at hm
    refine Submodule.neg_mem _ ?_
    convert hm using 2
    refine zmod2_cases p (h : ZMod 2) (fun P H => P * (H + 1) = P + H * P) ?_ ?_ ?_ ?_ <;>
      decide

end SuperRouquierLoc

namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D)

/-- The leftward cup `1 → Fᵢ Eᵢ` at the top weight of an `i`-edge, from the local data
centred there. -/
def leftCup (i : I) {x y : X} (h : x + D.α i = y) : 𝟙 (T.obj y) ⟶ T.F i h ≫ T.E i h :=
  (T.loc i h (rfl : y + D.α i = y + D.α i)).cupL

/-- The leftward cap `Eᵢ Fᵢ → 1` at the bottom weight of an `i`-edge, from the local data
centred there. -/
def leftCap (i : I) {x y : X} (h : x + D.α i = y) : T.E i h ≫ T.F i h ⟶ 𝟙 (T.obj x) :=
  (T.loc i (sub_add_cancel x (D.α i)) h).capL

theorem leftCup_mem (i : I) {x y : X} (h : x + D.α i = y) :
    T.leftCup i h ∈ parity (R := k) _ _ (leftAdjParity D i x) := by
  rw [← leftAdjParity_edge D i h]
  exact (T.loc i h rfl).cupL_mem

theorem leftCap_mem (i : I) {x y : X} (h : x + D.α i = y) :
    T.leftCap i h ∈ parity (R := k) _ _ (leftAdjParity D i x) :=
  (T.loc i (sub_add_cancel x (D.α i)) h).capL_mem

/-- The zigzag on `Fᵢ` of the leftward cup and cap. -/
def leftZigF (i : I) {x y : X} (h : x + D.α i = y) : T.F i h ⟶ T.F i h :=
  (leftUnitor (T.F i h)).inv ≫ T.leftCup i h ▷ T.F i h ≫
    (associator (T.F i h) (T.E i h) (T.F i h)).hom ≫ T.F i h ◁ T.leftCap i h ≫
    (rightUnitor (T.F i h)).hom

/-- The zigzag on `Eᵢ` of the leftward cup and cap. -/
def leftZigE (i : I) {x y : X} (h : x + D.α i = y) : T.E i h ⟶ T.E i h :=
  (rightUnitor (T.E i h)).inv ≫ T.E i h ◁ T.leftCup i h ≫
    (associator (T.E i h) (T.F i h) (T.E i h)).inv ≫ T.leftCap i h ▷ T.E i h ≫
    (leftUnitor (T.E i h)).hom

/-- **Open obligation** (super analogue of Brundan, Theorem 4.3): the leftward cup and
cap satisfy both zigzag identities up to a common unit `c`, with the sign `(-1)^σ`
on the `E`-zigzag. -/
def LeftZigzags : Prop :=
  ∀ (i : I) (x y : X) (h : x + D.α i = y), ∃ c : kˣ,
    T.leftZigF i h = (c : k) • 𝟙 _ ∧
      T.leftZigE i h = ((koszulSign (leftAdjParity D i x) (leftAdjParity D i x) : k) * c) • 𝟙 _

/-- The unit scalar of the zigzag obligation. -/
def zigUnit (H : T.LeftZigzags) (i : I) (x y : X) (h : x + D.α i = y) : kˣ :=
  (H i x y h).choose

omit [TwoSupercategory k B] in
theorem zigUnit_F (H : T.LeftZigzags) (i : I) (x y : X) (h : x + D.α i = y) :
    T.leftZigF i h = (T.zigUnit H i x y h : k) • 𝟙 _ :=
  (H i x y h).choose_spec.1

omit [TwoSupercategory k B] in
theorem zigUnit_E (H : T.LeftZigzags) (i : I) (x y : X) (h : x + D.α i = y) :
    T.leftZigE i h = ((koszulSign (leftAdjParity D i x) (leftAdjParity D i x) : k) *
      T.zigUnit H i x y h) • 𝟙 _ :=
  (H i x y h).choose_spec.2

/-- Normalizing the cap by `c⁻¹` turns the zigzag obligation into shifted left adjunctions. -/
def leftAdjointsOfZigzags (H : T.LeftZigzags) : RouquierLeftAdjoints (k := k) T where
  adjL i {x y} h :=
    { unit := T.leftCup i h
      counit := (((T.zigUnit H i x y h)⁻¹ : kˣ) : k) • T.leftCap i h
      unit_mem := T.leftCup_mem i h
      counit_mem := Submodule.smul_mem _ _ (T.leftCap_mem i h)
      left_triangle := by
        have hF := T.zigUnit_F H i x y h
        unfold leftZigF at hF
        rw [TwoSupercategory.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul,
          Linear.comp_smul, Linear.comp_smul, hF, smul_smul, Units.inv_mul, one_smul]
      right_triangle := by
        have hE := T.zigUnit_E H i x y h
        unfold leftZigE at hE
        rw [TwoSupercategory.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul,
          Linear.comp_smul, Linear.comp_smul, hE, smul_smul, mul_left_comm, Units.inv_mul,
          mul_one, Int.cast_smul_eq_zsmul] }

end RouquierFamily
end OddMath.SKM
