/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ColourBlock
import OddMath.Diagrams.OddNilHecke.Intertwiner

/-!
# Same-colour intertwiners of signed nilHecke families

Ports `Categorification/KLR/Intertwiner.lean` (Kang–Kashiwara, arXiv:1102.4677v4, (4.7) and
Lemma 4.12) to the quiver Hecke superalgebra, following Kang–Kashiwara–Oh, arXiv:1206.5933v2,
§8: the intertwiners `φ_a` of (8.7), their variants `g_a` of (8.8), the dot and far-crossing
identities of Lemma 8.3 ((8.11), (8.12)) and the product (8.15), on two adjacent strands of
one colour. The downstream consumer is the `QP` product of KKO Theorem 8.5 (the super analogue
of KK Theorem 4.15), which composes these elements on the words `(ν, i)`.

The statements are ring identities for a signed nilHecke family `X, T` with sign `ε`
(`IsSignedNilHeckeFamily`), so they apply to every same-colour block of a word in the quiver
Hecke supercategory (`isSignedNilHeckeFamily_block`, with `ε = (-1)^{|i|}`). With the relations
`T_j X_j - ε X_{j+1} T_j = 1 = X_j T_j - ε T_j X_{j+1}` of the family, KKO's crossing `τ_a` is
`-ε T_j`: it is `-T_j` on an even colour and `T_j` on an odd colour. Writing `u = X_j`,
`v = X_{j+1}`, the elements are

* even colour (`ε = 1`): `φ = 1 + (v - u) T_j` and `g = (v - u) φ`;
* odd colour (`ε = -1`): `φ = (v - u) - (v² - u²) T_j` and
  `g = (v² - u²) φ = OddNilHecke.Intertwiner.element u v T_j`, whose two-strand identities
  (`OddNilHecke.Intertwiner.identities`, `anticommutes`) are reused here.

## Main results

* `OddTwo`, `EvenTwo`: the two-strand relations; `oddTwo_block`, `evenTwo_block` provide them on
  two adjacent strands of one colour in any word, and `IsSignedNilHeckeFamily.oddTwo`,
  `evenTwo` on any adjacent pair of a block.
* Odd colour: `OddTwo.x_succ_mul_phiOdd`, `x_mul_phiOdd` (`v φ = -φ u`, `u φ = -φ v`: KKO (8.11)
  for `b = a, a + 1`), `phiOdd_mul_phiOdd` (`φ² = (v - u)²`), `element_identities` (for `g`),
  and the far identities `x_far_mul_phiOdd`, `t_far_mul_phiOdd`, `x_far_mul_element`,
  `t_far_mul_element` (KKO (8.11) for `b ≠ a, a + 1`, and (8.12)).
* Even colour: `EvenTwo.x_succ_mul_phiEven`, `x_mul_phiEven`, `x_succ_mul_gEven`,
  `x_mul_gEven`, `phiEven_mul_phiEven` (`φ² = 1`), `gEven_mul_gEven` (`g² = -(v - u)²`),
  `t_mul_gEven` (`T_j g = T_j (v - u)`, the first case of KKO (8.15) on equal colours), and
  `x_far_mul_phiEven`, `t_far_mul_phiEven`.

The braid identity `τ_a φ_{a+1} φ_a = φ_{a+1} φ_a τ_{a+1}` of Lemma 8.3, the case of distinct
colours, and the composite `g_n ⋯ g_1` are not treated here.
-/

namespace OddMath.QuiverHecke.SignedNilHecke

variable {B : Type*} [Ring B]

/-! ### Two strands of one colour -/

/-- The relations of the odd nilHecke ring on two strands, with dots `u, v` and crossing `T`. -/
structure OddTwo (u v T : B) : Prop where
  t_u : T * u + v * T = 1
  u_t : u * T + T * v = 1
  u_v : u * v = -(v * u)
  t_t : T * T = 0

/-- The relations of the nilHecke ring on two strands, with dots `u, v` and crossing `T`. -/
structure EvenTwo (u v T : B) : Prop where
  t_u : T * u - v * T = 1
  u_t : u * T - T * v = 1
  u_v : u * v = v * u
  t_t : T * T = 0

/-- The odd intertwiner `(v - u) - (v² - u²) T` (KKO (8.7), with `τ = T`). -/
def phiOdd (u v T : B) : B := (v - u) - (v * v - u * u) * T

/-- The even intertwiner `1 + (v - u) T` (KKO (8.7), with `τ = -T`). -/
def phiEven (u v T : B) : B := 1 + (v - u) * T

/-- The even variant `g = (v - u) φ` (KKO (8.8)). -/
def gEven (u v T : B) : B := (v - u) * phiEven u v T

namespace OddTwo

variable {u v T : B} (h : OddTwo u v T)
include h

theorem tu (r : B) : T * (u * r) = r - v * (T * r) := by
  rw [← mul_assoc, eq_sub_of_add_eq h.t_u, sub_mul, one_mul, mul_assoc]

theorem tu' : T * u = 1 - v * T := eq_sub_of_add_eq h.t_u

theorem tv (r : B) : T * (v * r) = r - u * (T * r) := by
  rw [← mul_assoc, eq_sub_of_add_eq' h.u_t, sub_mul, one_mul, mul_assoc]

theorem tv' : T * v = 1 - u * T := eq_sub_of_add_eq' h.u_t

theorem vu' : v * u = -(u * v) := by rw [h.u_v, neg_neg]

theorem vu (r : B) : v * (u * r) = -(u * (v * r)) := by
  rw [← mul_assoc, h.vu', neg_mul, mul_assoc]

theorem tt (r : B) : T * (T * r) = 0 := by rw [← mul_assoc, h.t_t, zero_mul]

theorem x_succ_mul_phiOdd : v * phiOdd u v T = -(phiOdd u v T * u) := by
  simp only [phiOdd, mul_sub, sub_mul, mul_assoc, mul_neg,
    h.tu', h.vu, h.vu', mul_one, neg_neg]
  noncomm_ring

theorem x_mul_phiOdd : u * phiOdd u v T = -(phiOdd u v T * v) := by
  simp only [phiOdd, mul_sub, sub_mul, mul_assoc, mul_neg,
    h.tv', h.vu, mul_one, neg_neg]
  noncomm_ring

theorem phiOdd_mul_phiOdd : phiOdd u v T * phiOdd u v T = (v - u) * (v - u) := by
  simp only [phiOdd, mul_sub, sub_mul, mul_assoc, mul_neg, h.tu,
    h.tu', h.tv, h.tv', h.vu, h.vu', h.t_t, mul_one, mul_zero, neg_neg]
  noncomm_ring

/-- KKO (8.8), (8.11) and (8.15) for the odd variant `g = (v² - u²)((v - u) - (v² - u²) T)`
(`OddNilHecke.Intertwiner.element`): its square, the two dot transports, and `T g`. -/
theorem element_identities :
    OddNilHecke.Intertwiner.element u v T ^ 2 =
        -(OddNilHecke.Intertwiner.squareDiff u v ^ 2 * (u ^ 2 + v ^ 2)) ∧
      OddNilHecke.Intertwiner.element u v T * u = -(v * OddNilHecke.Intertwiner.element u v T) ∧
      OddNilHecke.Intertwiner.element u v T * v = -(u * OddNilHecke.Intertwiner.element u v T) ∧
      OddNilHecke.Intertwiner.element u v T =
        -((T * OddNilHecke.Intertwiner.squareDiff u v - (v - u)) *
          OddNilHecke.Intertwiner.squareDiff u v) ∧
      T * OddNilHecke.Intertwiner.element u v T =
        T * (v - u) * OddNilHecke.Intertwiner.squareDiff u v :=
  OddNilHecke.Intertwiner.identities u v T h.t_t (by rw [h.u_v, neg_add_cancel]) h.t_u h.u_t

end OddTwo

/-- An element anticommuting with `u`, `v` and `T` anticommutes with the odd intertwiner. -/
theorem anticomm_phiOdd {u v T Y : B} (hu : Y * u = -(u * Y)) (hv : Y * v = -(v * Y))
    (hT : Y * T = -(T * Y)) : Y * phiOdd u v T = -(phiOdd u v T * Y) := by
  have hu' (r : B) : Y * (u * r) = -(u * (Y * r)) := by rw [← mul_assoc, hu, neg_mul, mul_assoc]
  have hv' (r : B) : Y * (v * r) = -(v * (Y * r)) := by rw [← mul_assoc, hv, neg_mul, mul_assoc]
  have hT' (r : B) : Y * (T * r) = -(T * (Y * r)) := by rw [← mul_assoc, hT, neg_mul, mul_assoc]
  simp only [phiOdd, mul_sub, sub_mul, mul_assoc, mul_neg, hu', hv', hu, hv, hT, neg_neg]
  noncomm_ring

/-- An element commuting with `u`, `v` and `T` commutes with the even intertwiner. -/
theorem comm_phiEven {u v T Y : B} (hu : Y * u = u * Y) (hv : Y * v = v * Y)
    (hT : Y * T = T * Y) : Y * phiEven u v T = phiEven u v T * Y := by
  have hu' (r : B) : Y * (u * r) = u * (Y * r) := by rw [← mul_assoc, hu, mul_assoc]
  have hv' (r : B) : Y * (v * r) = v * (Y * r) := by rw [← mul_assoc, hv, mul_assoc]
  simp only [phiEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc, mul_one, one_mul, hu', hv',
    hT]

/-- An element commuting with `u`, `v` and `T` commutes with the even variant `g`. -/
theorem comm_gEven {u v T Y : B} (hu : Y * u = u * Y) (hv : Y * v = v * Y)
    (hT : Y * T = T * Y) : Y * gEven u v T = gEven u v T * Y := by
  rw [gEven, ← mul_assoc, mul_sub, hv, hu, ← sub_mul, mul_assoc, comm_phiEven hu hv hT,
    mul_assoc]

namespace EvenTwo

variable {u v T : B} (h : EvenTwo u v T)
include h

theorem tu' : T * u = 1 + v * T := by rw [← h.t_u, sub_add_cancel]

theorem tu (r : B) : T * (u * r) = r + v * (T * r) := by
  rw [← mul_assoc, h.tu', add_mul, one_mul, mul_assoc]

theorem tv' : T * v = u * T - 1 := by rw [← h.u_t, sub_sub_cancel]

theorem tv (r : B) : T * (v * r) = u * (T * r) - r := by
  rw [← mul_assoc, h.tv', sub_mul, one_mul, mul_assoc]

theorem vu' : v * u = u * v := h.u_v.symm

theorem vu (r : B) : v * (u * r) = u * (v * r) := by rw [← mul_assoc, h.vu', mul_assoc]

theorem tt (r : B) : T * (T * r) = 0 := by rw [← mul_assoc, h.t_t, zero_mul]

theorem x_succ_mul_phiEven : v * phiEven u v T = phiEven u v T * u := by
  simp only [phiEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    h.tu', h.vu, mul_one, one_mul]
  noncomm_ring

theorem x_mul_phiEven : u * phiEven u v T = phiEven u v T * v := by
  simp only [phiEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    h.tv', h.vu, mul_one, one_mul]
  noncomm_ring

theorem phiEven_mul_phiEven : phiEven u v T * phiEven u v T = 1 := by
  simp only [phiEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    h.tu, h.tv, h.t_t, mul_one, one_mul, mul_zero]
  noncomm_ring

theorem t_mul_gEven : T * gEven u v T = T * (v - u) := by
  simp only [phiEven, gEven, mul_add, mul_sub, sub_mul,
    h.tu, h.tu', h.tv, h.tv', h.vu, h.t_t, mul_one, mul_zero]
  noncomm_ring

theorem gEven_mul_gEven : gEven u v T * gEven u v T = -((v - u) * (v - u)) := by
  simp only [phiEven, gEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    h.tu, h.tu', h.tv, h.tv', h.vu, h.vu', h.t_t, mul_one, mul_zero]
  noncomm_ring

theorem x_succ_mul_gEven : v * gEven u v T = gEven u v T * u := by
  simp only [phiEven, gEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    h.tu', h.vu, h.vu', mul_one]
  noncomm_ring

theorem x_mul_gEven : u * gEven u v T = gEven u v T * v := by
  simp only [phiEven, gEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    h.tv', h.vu, mul_one]
  noncomm_ring

end EvenTwo

/-! ### Positions of a signed nilHecke family -/

theorem neg_of_neg_one_smul {x y : B} (h : x * y = ((-1 : ℤˣ) : ℤ) • (y * x)) :
    x * y = -(y * x) := by
  simpa only [Units.val_neg, Units.val_one, neg_smul, one_smul] using h

theorem swap_of_neg_one_smul {x y : B} (h : x * y = ((-1 : ℤˣ) : ℤ) • (y * x)) :
    y * x = -(x * y) := by
  rw [neg_of_neg_one_smul h, neg_neg]

theorem eq_of_one_smul {x y : B} (h : x * y = ((1 : ℤˣ) : ℤ) • (y * x)) : x * y = y * x := by
  simpa only [Units.val_one, one_smul] using h

namespace IsSignedNilHeckeFamily

variable {s n : ℕ} {X T : ℕ → B}

/-- Two adjacent strands of an odd block satisfy the odd two-strand relations. -/
theorem oddTwo (hF : IsSignedNilHeckeFamily (-1) s n X T) {j : ℕ} (h₁ : s ≤ j)
    (h₂ : j + 1 < s + n) : OddTwo (X j) (X (j + 1)) (T j) where
  t_u := by
    simpa only [Units.val_neg, Units.val_one, neg_smul, one_smul, sub_neg_eq_add] using
      hF.t_x j h₁ h₂
  u_t := by
    simpa only [Units.val_neg, Units.val_one, neg_smul, one_smul, sub_neg_eq_add] using
      hF.x_t j h₁ h₂
  u_v := neg_of_neg_one_smul (hF.x_comm j (j + 1) h₁ (by omega) (by omega) h₂ (by omega))
  t_t := hF.t_sq j h₁ h₂

/-- Two adjacent strands of an even block satisfy the nilHecke two-strand relations. -/
theorem evenTwo (hF : IsSignedNilHeckeFamily 1 s n X T) {j : ℕ} (h₁ : s ≤ j)
    (h₂ : j + 1 < s + n) : EvenTwo (X j) (X (j + 1)) (T j) where
  t_u := by simpa only [Units.val_one, one_smul] using hF.t_x j h₁ h₂
  u_t := by simpa only [Units.val_one, one_smul] using hF.x_t j h₁ h₂
  u_v := eq_of_one_smul (hF.x_comm j (j + 1) h₁ (by omega) (by omega) h₂ (by omega))
  t_t := hF.t_sq j h₁ h₂

/-- KKO (8.11), `b ≠ a, a + 1`, odd colour: a dot away from strands `j, j + 1` anticommutes
with the intertwiner `φ_j`. -/
theorem x_far_mul_phiOdd (hF : IsSignedNilHeckeFamily (-1) s n X T) {a j : ℕ} (ha₁ : s ≤ a)
    (ha₂ : a < s + n) (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (h₃ : a ≠ j) (h₄ : a ≠ j + 1) :
    X a * phiOdd (X j) (X (j + 1)) (T j) = -(phiOdd (X j) (X (j + 1)) (T j) * X a) :=
  anticomm_phiOdd (neg_of_neg_one_smul (hF.x_comm a j ha₁ ha₂ h₁ (by omega) h₃))
    (neg_of_neg_one_smul (hF.x_comm a (j + 1) ha₁ ha₂ (by omega) h₂ h₄))
    (neg_of_neg_one_smul (hF.x_t_comm a j ha₁ ha₂ h₁ h₂ h₃ h₄))

/-- KKO (8.11), `b ≠ a, a + 1`, odd colour, for the variant `g_j`. -/
theorem x_far_mul_element (hF : IsSignedNilHeckeFamily (-1) s n X T) {a j : ℕ}
    (ha₁ : s ≤ a) (ha₂ : a < s + n) (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (h₃ : a ≠ j)
    (h₄ : a ≠ j + 1) :
    X a * OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j) =
      -(OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j) * X a) :=
  OddNilHecke.Intertwiner.anticommutes _ _ _ _ (neg_of_neg_one_smul (hF.x_comm a j ha₁ ha₂ h₁ (by omega) h₃))
    (neg_of_neg_one_smul (hF.x_comm a (j + 1) ha₁ ha₂ (by omega) h₂ h₄))
    (neg_of_neg_one_smul (hF.x_t_comm a j ha₁ ha₂ h₁ h₂ h₃ h₄))

/-- KKO (8.12), odd colour: a crossing far from strands `j, j + 1` anticommutes with `φ_j`. -/
theorem t_far_mul_phiOdd (hF : IsSignedNilHeckeFamily (-1) s n X T) {j l : ℕ} (h₁ : s ≤ j)
    (h₂ : j + 1 < s + n) (hl₁ : s ≤ l) (hl₂ : l + 1 < s + n) (hjl : j + 1 < l ∨ l + 1 < j) :
    T l * phiOdd (X j) (X (j + 1)) (T j) = -(phiOdd (X j) (X (j + 1)) (T j) * T l) := by
  refine anticomm_phiOdd
    (swap_of_neg_one_smul (hF.x_t_comm j l h₁ (by omega) hl₁ hl₂ (by omega) (by omega)))
    (swap_of_neg_one_smul (hF.x_t_comm (j + 1) l (by omega) h₂ hl₁ hl₂ (by omega) (by omega))) ?_
  rcases hjl with h | h
  · exact swap_of_neg_one_smul (hF.t_comm j l h₁ h hl₂)
  · exact neg_of_neg_one_smul (hF.t_comm l j hl₁ h h₂)

/-- KKO (8.12), odd colour, for the variant `g_j`. -/
theorem t_far_mul_element (hF : IsSignedNilHeckeFamily (-1) s n X T) {j l : ℕ}
    (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (hl₁ : s ≤ l) (hl₂ : l + 1 < s + n)
    (hjl : j + 1 < l ∨ l + 1 < j) :
    T l * OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j) =
      -(OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j) * T l) := by
  refine OddNilHecke.Intertwiner.anticommutes _ _ _ _
    (swap_of_neg_one_smul (hF.x_t_comm j l h₁ (by omega) hl₁ hl₂ (by omega) (by omega)))
    (swap_of_neg_one_smul (hF.x_t_comm (j + 1) l (by omega) h₂ hl₁ hl₂ (by omega) (by omega))) ?_
  rcases hjl with h | h
  · exact swap_of_neg_one_smul (hF.t_comm j l h₁ h hl₂)
  · exact neg_of_neg_one_smul (hF.t_comm l j hl₁ h h₂)

/-- KKO (8.11), `b ≠ a, a + 1`, even colour. -/
theorem x_far_mul_phiEven (hF : IsSignedNilHeckeFamily 1 s n X T) {a j : ℕ} (ha₁ : s ≤ a)
    (ha₂ : a < s + n) (h₁ : s ≤ j) (h₂ : j + 1 < s + n) (h₃ : a ≠ j) (h₄ : a ≠ j + 1) :
    X a * phiEven (X j) (X (j + 1)) (T j) = phiEven (X j) (X (j + 1)) (T j) * X a :=
  comm_phiEven (eq_of_one_smul (hF.x_comm a j ha₁ ha₂ h₁ (by omega) h₃))
    (eq_of_one_smul (hF.x_comm a (j + 1) ha₁ ha₂ (by omega) h₂ h₄))
    (eq_of_one_smul (hF.x_t_comm a j ha₁ ha₂ h₁ h₂ h₃ h₄))

/-- KKO (8.12), even colour. -/
theorem t_far_mul_phiEven (hF : IsSignedNilHeckeFamily 1 s n X T) {j l : ℕ} (h₁ : s ≤ j)
    (h₂ : j + 1 < s + n) (hl₁ : s ≤ l) (hl₂ : l + 1 < s + n) (hjl : j + 1 < l ∨ l + 1 < j) :
    T l * phiEven (X j) (X (j + 1)) (T j) = phiEven (X j) (X (j + 1)) (T j) * T l := by
  refine comm_phiEven
    (eq_of_one_smul (hF.x_t_comm j l h₁ (by omega) hl₁ hl₂ (by omega) (by omega))).symm
    (eq_of_one_smul (hF.x_t_comm (j + 1) l (by omega) h₂ hl₁ hl₂ (by omega) (by omega))).symm ?_
  rcases hjl with h | h
  · exact (eq_of_one_smul (hF.t_comm j l h₁ h hl₂)).symm
  · exact eq_of_one_smul (hF.t_comm l j hl₁ h h₂)

end IsSignedNilHeckeFamily

end OddMath.QuiverHecke.SignedNilHecke

/-! ### Same-colour blocks of words -/

namespace OddMath.QuiverHecke

open SignedNilHecke

variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- Two adjacent strands of an odd colour `i` in a word satisfy the odd two-strand relations. -/
theorem oddTwo_block (pre post : List I) (i : I) (hi : D.parity i = 1) :
    OddTwo (dotE D Sc (pre ++ [i, i] ++ post) pre.length)
      (dotE D Sc (pre ++ [i, i] ++ post) (pre.length + 1))
      (crossE D Sc (pre ++ [i, i] ++ post) pre.length) := by
  have hF := isSignedNilHeckeFamily_block D Sc pre post i 2
  rw [hi, show zunit (1 : ZMod 2) = -1 by simp [zunit]] at hF
  exact hF.oddTwo le_rfl (by omega)

/-- Two adjacent strands of an even colour `i` in a word satisfy the nilHecke relations. -/
theorem evenTwo_block (pre post : List I) (i : I) (hi : D.parity i = 0) :
    EvenTwo (dotE D Sc (pre ++ [i, i] ++ post) pre.length)
      (dotE D Sc (pre ++ [i, i] ++ post) (pre.length + 1))
      (crossE D Sc (pre ++ [i, i] ++ post) pre.length) := by
  have hF := isSignedNilHeckeFamily_block D Sc pre post i 2
  rw [hi, show zunit (0 : ZMod 2) = 1 by simp [zunit]] at hF
  exact hF.evenTwo le_rfl (by omega)

end OddMath.QuiverHecke
