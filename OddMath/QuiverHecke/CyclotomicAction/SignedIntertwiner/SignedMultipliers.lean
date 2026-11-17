import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import OddMath.Diagrams.OddNilHecke.DotTranslation
import OddMath.Diagrams.OddNilHecke.Intertwiner
import OddMath.QuiverHecke.Centre
import OddMath.QuiverHecke.ColourBlock
import OddMath.QuiverHecke.MixedRelations
import OddMath.SKM.Grading
import OddMath.SKM.SerrePolynomial

/-!
# Signed intertwiner

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Signed right multipliers and the mixed quadratic sign

For odd `u`, signed right multiplication on a regular supermodule is
`h ↦ σ(h) * u`, where `σ` is the parity involution. Its square is minus
right multiplication by `u²`. In particular, negating both crossings does
not repair a mixed odd/odd quadratic relation with nonzero constant term.

The rational four-dimensional example is the regular module of two-by-two
matrices, with even diagonal word idempotents and odd off-diagonal crossings.
Taking both dots zero gives the two-distinct-colour, zero-edge, cutoff-one
quadratic block. It isolates the mixed quadratic sign; it is not an action
of the entire quiver Hecke category. No projectivity or
cyclotomic action is asserted here.
-/
namespace OddMath.QuiverHecke.CyclotomicAction

variable {A : Type*} [Ring A]

/-- Signed right multiplication by an odd homogeneous element. -/
def oddRight (σ : A →+* A) (u h : A) : A := σ h * u

/-- The super-opposite sign for two odd right multipliers, including their order. -/
theorem oddRight_comp (σ : A →+* A) (hσ : Function.Involutive σ)
    (u v : A) (hv : σ v = -v) (h : A) :
    oddRight σ u (oddRight σ v h) = -(h * (v * u)) := by
  simp only [oddRight, map_mul, hσ h, hv, mul_neg, neg_mul, mul_assoc]

/-- A simultaneous minus on both odd crossings leaves the quadratic sign unchanged. -/
theorem neg_oddRight_comp (σ : A →+* A) (hσ : Function.Involutive σ)
    (u v : A) (hv : σ v = -v) (h : A) :
    -oddRight σ u (-oddRight σ v h) = -(h * (v * u)) := by
  simpa only [oddRight, map_neg, neg_mul, neg_neg] using oddRight_comp σ hσ u v hv h

end OddMath.QuiverHecke.CyclotomicAction

end

section

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

* `braid_phiOdd`, `braid_element`, `braid_phiEven`, `braid_gEven`: the braid identity
  `τ_a φ_{a+1} φ_a = φ_{a+1} φ_a τ_{a+1}` of Lemma 8.3 on three strands of one colour (the sign
  of `τ` cancels), and the same identity for the variants `g`.

Strands of distinct colours, and the composite `g_n ⋯ g_1`, are not treated here.
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

theorem mul_mul_of_mul_eq {x y z : B} (h : x * y = z) (r : B) : x * (y * r) = z * r := by
  rw [← mul_assoc, h]

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

/-- The braid identity of KKO Lemma 8.3 for the odd variants `g`. -/
theorem braid_element (hF : IsSignedNilHeckeFamily (-1) s n X T) {j : ℕ} (h₁ : s ≤ j)
    (h₂ : j + 2 < s + n) :
    T j * (OddNilHecke.Intertwiner.element (X (j + 1)) (X (j + 2)) (T (j + 1)) *
        OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j)) =
      OddNilHecke.Intertwiner.element (X (j + 1)) (X (j + 2)) (T (j + 1)) *
        OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j) * T (j + 1) := by
  have o₁ := hF.oddTwo h₁ (by omega)
  have o₂ : OddTwo (X (j + 1)) (X (j + 2)) (T (j + 1)) := hF.oddTwo (j := j + 1) (by omega) h₂
  have h₃ : T j * X (j + 2) = -(X (j + 2) * T j) := swap_of_neg_one_smul
    (hF.x_t_comm (j + 2) j (by omega) (by omega) h₁ (by omega) (by omega) (by omega))
  have h₆ : T (j + 1) * X j = -(X j * T (j + 1)) := swap_of_neg_one_smul
    (hF.x_t_comm j (j + 1) h₁ (by omega) (by omega) (by omega) (by omega) (by omega))
  have h₈ : X (j + 2) * X j = -(X j * X (j + 2)) := neg_of_neg_one_smul
    (hF.x_comm (j + 2) j (by omega) (by omega) h₁ (by omega) (by omega))
  have hss := hF.t_sq j h₁ (by omega)
  have huu := hF.t_sq (j + 1) (by omega) (by omega)
  have hb : T (j + 1) * (T j * T (j + 1)) = T j * (T (j + 1) * T j) := by
    simpa only [mul_assoc] using (hF.braid j h₁ h₂).symm
  simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff, pow_two,
    mul_sub, sub_mul, mul_assoc, mul_neg, neg_mul,
    neg_neg, mul_one, mul_zero, o₁.tu, o₁.tv, o₁.tv', o₂.tu, o₂.tu',
    o₁.vu, o₁.vu', o₂.vu, o₂.vu', h₃, mul_mul_of_mul_eq h₃, h₆,
    mul_mul_of_mul_eq h₆, h₈, mul_mul_of_mul_eq h₈, hss, huu,
    hb]
  noncomm_ring

/-- The braid identity of KKO Lemma 8.3 for the even variants `g`. -/
theorem braid_gEven (hF : IsSignedNilHeckeFamily 1 s n X T) {j : ℕ} (h₁ : s ≤ j)
    (h₂ : j + 2 < s + n) :
    T j * (gEven (X (j + 1)) (X (j + 2)) (T (j + 1)) * gEven (X j) (X (j + 1)) (T j)) =
      gEven (X (j + 1)) (X (j + 2)) (T (j + 1)) * gEven (X j) (X (j + 1)) (T j) * T (j + 1) := by
  have o₁ := hF.evenTwo h₁ (by omega)
  have o₂ : EvenTwo (X (j + 1)) (X (j + 2)) (T (j + 1)) := hF.evenTwo (j := j + 1) (by omega) h₂
  have h₃ : T j * X (j + 2) = X (j + 2) * T j := (eq_of_one_smul
    (hF.x_t_comm (j + 2) j (by omega) (by omega) h₁ (by omega) (by omega) (by omega))).symm
  have h₆ : T (j + 1) * X j = X j * T (j + 1) := (eq_of_one_smul
    (hF.x_t_comm j (j + 1) h₁ (by omega) (by omega) (by omega) (by omega) (by omega))).symm
  have h₈ : X (j + 2) * X j = X j * X (j + 2) := eq_of_one_smul
    (hF.x_comm (j + 2) j (by omega) (by omega) h₁ (by omega) (by omega))
  have hss := hF.t_sq j h₁ (by omega)
  have huu := hF.t_sq (j + 1) (by omega) (by omega)
  have hb : T (j + 1) * (T j * T (j + 1)) = T j * (T (j + 1) * T j) := by
    simpa only [mul_assoc] using (hF.braid j h₁ h₂).symm
  simp only [gEven, phiEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    mul_one, mul_zero, o₁.tu, o₁.tv, o₁.tv', o₂.tu, o₂.tu',
    o₁.vu, o₁.vu', o₂.vu, o₂.vu', h₃, mul_mul_of_mul_eq h₃, h₆,
    mul_mul_of_mul_eq h₆, h₈, mul_mul_of_mul_eq h₈, hss, huu,
    hb]
  noncomm_ring

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

end

section

/-!
# Intertwiners between words and the adjacent dot transport

Ports the word-level use of `Categorification/KLR/Intertwiner.lean` (`KLRAlgebra.gInt` and
`x_mul_gInt`, Kang–Kashiwara arXiv:1102.4677v4, (4.7) and the first identity of Lemma 4.12) to
the quiver Hecke supercategory, following Kang–Kashiwara–Oh, arXiv:1206.5933v2, (8.8) and the
second identity of Lemma 8.3 (8.11) for `b = a, a + 1`. The downstream consumer is the map `Q`
of KKO Proposition 8.4 and the product `QP` of Theorem 8.5, which compose the intertwiners
`g_n ⋯ g_1` on the words `(i, ν)`.

For a word `l ++ [i, j] ++ r`, `intertwinerHom l r i j` is KKO's `g_a e(ν)` at `a = |l|`, as a
morphism to `l ++ [j, i] ++ r`:

* the crossing, if `i ≠ j`;
* `(v - u)(1 + (v - u) T)` on an even colour and `OddNilHecke.Intertwiner.element u v T`
  `= (v² - u²)((v - u) - (v² - u²) T)` on an odd colour, if `i = j`, with `u, v` the dots on the
  two strands and `T` their crossing (`CyclotomicAction.Intertwiner`).

Diagrams compose bottom to top. The dot on the left strand passes through `g` to the right
strand with the sign `(-1)^{|i||j|}`, and the dot on the right strand to the left one with the
same sign (`dot_comp_intertwinerHom`, `dot_succ_comp_intertwinerHom`); this is KKO's sign
`(-1)^{p(ν_a)p(ν_{a+1})p(ν_b)}` for `b = a, a + 1`.

`moveHom i l ν` is the composite `g_{|l|+|ν|} ⋯ g_{|l|+1}` from `l ++ i :: ν` to
`l ++ ν ++ [i]`, which for `l = []` is the element `g_n ⋯ g_1 e(i, ν)` of KKO's map `Q`
(Proposition 8.4). `dot_comp_moveHom` is the second identity of KKO (8.13):
`x_{n+1} g_n ⋯ g_1 e(i, ν) = (-1)^{p(i)p(ν)} g_n ⋯ g_1 x_1 e(i, ν)`.

Dots away from the pair pass through `g` with the sign `(-1)^{p(ν_b)p(ν_a)p(ν_{a+1})}`
(`dot_left_comp_intertwinerHom`, `dot_right_comp_intertwinerHom`: (8.11) for
`b ≠ a, a + 1`). Hence a dot on the strand `ν_b` passes through `g_n ⋯ g_1` from position
`b + 1` to position `b` with the sign `(-1)^{p(ν_b)p(i)p(ν)}` (`dot_mem_comp_moveHom`), which is
the first identity of (8.13) for the dots of `R(β)`; dots to the left of the moving strand pass
unchanged up to the same sign (`dot_left_comp_moveHom`).
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke
open SKM (zsign)
open scoped Classical

variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- KKO's `g_a` on two adjacent strands `a, a + 1` of one colour `i` in the word `w`. -/
def sameIntertwiner (w : List I) (a : ℕ) (i : I) : End ((pres D Sc).obj (ob D w)) :=
  if D.parity i = 1 then
    OddNilHecke.Intertwiner.element (dotE D Sc w a) (dotE D Sc w (a + 1)) (crossE D Sc w a)
  else gEven (dotE D Sc w a) (dotE D Sc w (a + 1)) (crossE D Sc w a)

theorem sChain_crossAt (l r : List I) (i j : I) :
    SChain (l ++ [i, j] ++ r) (pl (l ++ [i, j] ++ r) [.cross l.length]) (l ++ [j, i] ++ r) := by
  have h := sChain_pl (l ++ [i, j] ++ r) [.cross l.length]
  simpa [tgt, PG.act, List.take_append, List.drop_append] using h

theorem sChain_dotAt (l r : List I) (i j : I) (b : ℕ) :
    SChain (l ++ [i, j] ++ r) (pl (l ++ [i, j] ++ r) [.dot b]) (l ++ [i, j] ++ r) := by
  have h := sChain_pl (l ++ [i, j] ++ r) [.dot b]
  simpa [tgt, PG.act] using h

theorem dotE_eq_cl {w : List I} {b : ℕ} (h : SChain w (pl w [.dot b]) w) :
    dotE D Sc w b = cl D Sc w w [.dot b] h :=
  genE_eq D Sc h

/-- KKO's `g_a e(ν)` for `ν = l ++ [i, j] ++ r` and `a = |l|`, as a morphism of words. -/
def intertwinerHom (l r : List I) (i j : I) :
    (pres D Sc).obj (ob D (l ++ [i, j] ++ r)) ⟶ (pres D Sc).obj (ob D (l ++ [j, i] ++ r)) :=
  if h : i = j then
    sameIntertwiner D Sc (l ++ [i, j] ++ r) l.length i ≫ eqToHom (by rw [h])
  else cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i j)

theorem intertwinerHom_of_ne (l r : List I) {i j : I} (h : i ≠ j) :
    intertwinerHom D Sc l r i j = cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i j) := by
  simp [intertwinerHom, h]

theorem intertwinerHom_self (l r : List I) (i : I) :
    intertwinerHom D Sc l r i i = sameIntertwiner D Sc (l ++ [i, i] ++ r) l.length i := by
  simp [intertwinerHom]

theorem parity_eq_zero_of_ne_one {p : ZMod 2} (h : ¬p = 1) : p = 0 := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  exact (hz p).resolve_right h

/-- KKO (8.11) for `b = a`: the dot on the left strand passes to the right strand. -/
theorem dot_comp_intertwinerHom (l r : List I) (i j : I) :
    dotE D Sc (l ++ [i, j] ++ r) l.length ≫ intertwinerHom D Sc l r i j =
      zsign k (D.parity i * D.parity j) •
        (intertwinerHom D Sc l r i j ≫ dotE D Sc (l ++ [j, i] ++ r) (l.length + 1)) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, ← End.mul_def, ← End.mul_def]
    by_cases hp : D.parity i = 1
    · simp only [sameIntertwiner, hp, ite_true]
      rw [(oddTwo_block D Sc l r i hp).element_identities.2.1]
      simp [zsign]
    · have hp0 := parity_eq_zero_of_ne_one hp
      simp only [sameIntertwiner, hp, ite_false]
      rw [(evenTwo_block D Sc l r i hp0).x_succ_mul_gEven]
      simp [zsign, hp0]
  · rw [intertwinerHom_of_ne D Sc l r h,
      dotE_eq_cl D Sc (sChain_dotAt l r i j l.length),
      dotE_eq_cl D Sc (sChain_dotAt l r j i (l.length + 1)), cl_comp, cl_comp]
    exact slide_left_ne D Sc l r i j h _ _

/-- KKO (8.11) for `b = a + 1`: the dot on the right strand passes to the left strand. -/
theorem dot_succ_comp_intertwinerHom (l r : List I) (i j : I) :
    dotE D Sc (l ++ [i, j] ++ r) (l.length + 1) ≫ intertwinerHom D Sc l r i j =
      zsign k (D.parity i * D.parity j) •
        (intertwinerHom D Sc l r i j ≫ dotE D Sc (l ++ [j, i] ++ r) l.length) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, ← End.mul_def, ← End.mul_def]
    by_cases hp : D.parity i = 1
    · simp only [sameIntertwiner, hp, ite_true]
      rw [(oddTwo_block D Sc l r i hp).element_identities.2.2.1]
      simp [zsign]
    · have hp0 := parity_eq_zero_of_ne_one hp
      simp only [sameIntertwiner, hp, ite_false]
      rw [← (evenTwo_block D Sc l r i hp0).x_mul_gEven]
      simp [zsign, hp0]
  · rw [intertwinerHom_of_ne D Sc l r h,
      dotE_eq_cl D Sc (sChain_dotAt l r i j (l.length + 1)),
      dotE_eq_cl D Sc (sChain_dotAt l r j i l.length), cl_comp, cl_comp]
    have hs := slide_right_ne D Sc l r i j h (sChain_append_of (sChain_crossAt l r i j)
      (sChain_dotAt l r j i l.length))
      (sChain_append_of (sChain_dotAt l r i j (l.length + 1)) (sChain_crossAt l r i j))
    have h' := congrArg (zsign k (D.parity i * D.parity j) • ·) hs
    simp only [smul_smul, zsign_mul_self, one_smul] at h'
    exact h'.symm

/-! ### Moving a strand across a word -/

theorem zsign_add_eq (p q : ZMod 2) : zsign k (p + q) = zsign k p * zsign k q := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz p with rfl | rfl <;> rcases hz q with rfl | rfl <;> simp [zsign]

/-- A dot commutes with the identification of equal words. -/
theorem dotE_comp_eqToHom {w w' : List I} (h : w = w') (b : ℕ) :
    dotE D Sc w b ≫ eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫ dotE D Sc w' b := by
  subst h
  simp

/-- KKO's `g_n ⋯ g_1 e(i, ν)`, moving the strand of colour `i` from position `|l|` across
`ν` to the end: `g_{|l|+|ν|} ⋯ g_{|l|+1}` on `l ++ i :: ν`. -/
def moveHom (i : I) : (l ν : List I) →
    (pres D Sc).obj (ob D (l ++ i :: ν)) ⟶ (pres D Sc).obj (ob D (l ++ ν ++ [i]))
  | l, [] => eqToHom (by simp)
  | l, j :: ν =>
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp)) ≫
        intertwinerHom D Sc l ν i j ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp)) ≫
            moveHom i (l ++ [j]) ν ≫
              eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp))

/-- The parity `p(ν)` of a word. -/
def wordSumParity (ν : List I) : ZMod 2 := (ν.map D.parity).sum

/-- KKO (8.13), second identity: the dot on the moving strand passes from its first position
to the last, with the sign `(-1)^{p(i) p(ν)}`. -/
theorem dot_comp_moveHom (i : I) (l ν : List I) :
    dotE D Sc (l ++ i :: ν) l.length ≫ moveHom D Sc i l ν =
      zsign k (D.parity i * wordSumParity D ν) •
        (moveHom D Sc i l ν ≫ dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length)) := by
  induction ν generalizing l with
  | nil =>
    simp only [moveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero, List.length_nil,
      add_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul]
    exact dotE_comp_eqToHom D Sc (by simp) _
  | cons j ν ih =>
    simp only [moveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc (show l ++ i :: j :: ν = l ++ [i, j] ++ ν by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp),
      Category.assoc, show l.length + 1 = (l ++ [j]).length by simp,
      ← Category.assoc (dotE D Sc _ _), ih, Linear.smul_comp, Category.assoc,
      show (l ++ [j]).length + ν.length = l.length + (j :: ν).length by simp; omega,
      dotE_comp_eqToHom D Sc (show l ++ [j] ++ ν ++ [i] = l ++ j :: ν ++ [i] by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq]

/-! ### Far dots -/

section Ring
variable {B : Type*} [Ring B]

/-- An element commuting with `u`, `v`, `T` commutes with both same-colour variants. -/
theorem comm_variants {u v T Y : B} (hu : u * Y = Y * u) (hv : v * Y = Y * v)
    (ht : T * Y = Y * T) :
    OddNilHecke.Intertwiner.element u v T * Y = Y * OddNilHecke.Intertwiner.element u v T ∧
      gEven u v T * Y = Y * gEven u v T := by
  have hu' : ∀ r, u * (Y * r) = Y * (u * r) := fun r => by rw [← mul_assoc, hu, mul_assoc]
  have hv' : ∀ r, v * (Y * r) = Y * (v * r) := fun r => by rw [← mul_assoc, hv, mul_assoc]
  have ht' : ∀ r, T * (Y * r) = Y * (T * r) := fun r => by rw [← mul_assoc, ht, mul_assoc]
  constructor
  · simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff, pow_two,
      mul_sub, sub_mul, mul_assoc, hu, hv, ht, hu', hv']
  · simp only [gEven, phiEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc, mul_one,
      hu, hv, ht, hu', hv']

/-- An element anticommuting with `u`, `v`, `T` anticommutes with both same-colour variants. -/
theorem anticomm_variants {u v T Y : B} (hu : u * Y = -(Y * u)) (hv : v * Y = -(Y * v))
    (ht : T * Y = -(Y * T)) :
    OddNilHecke.Intertwiner.element u v T * Y = -(Y * OddNilHecke.Intertwiner.element u v T) ∧
      gEven u v T * Y = -(Y * gEven u v T) := by
  have hu' : ∀ r, u * (Y * r) = -(Y * (u * r)) := fun r => by
    rw [← mul_assoc, hu, neg_mul, mul_assoc]
  have hv' : ∀ r, v * (Y * r) = -(Y * (v * r)) := fun r => by
    rw [← mul_assoc, hv, neg_mul, mul_assoc]
  have ht' : ∀ r, T * (Y * r) = -(Y * (T * r)) := fun r => by
    rw [← mul_assoc, ht, neg_mul, mul_assoc]
  constructor
  · simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff, pow_two,
      mul_sub, sub_mul, mul_assoc, mul_neg, neg_neg, hu, hv, ht, hu',
      hv']
    noncomm_ring
  · simp only [gEven, phiEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc, mul_one,
      mul_neg, neg_neg, hu, hv, ht, hu', hv']
    noncomm_ring

end Ring

/-- If `u`, `v`, `T` all supercommute with `Y` with the sign of `q`, so does `g`. -/
theorem sameIntertwiner_mul_of {w : List I} {a : ℕ} {i : I} {Y : End ((pres D Sc).obj (ob D w))}
    (q : ZMod 2) (hu : dotE D Sc w a * Y = zsign k q • (Y * dotE D Sc w a))
    (hv : dotE D Sc w (a + 1) * Y = zsign k q • (Y * dotE D Sc w (a + 1)))
    (ht : crossE D Sc w a * Y = zsign k q • (Y * crossE D Sc w a)) :
    sameIntertwiner D Sc w a i * Y = zsign k q • (Y * sameIntertwiner D Sc w a i) := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz q with rfl | rfl
  · simp only [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul] at hu hv ht ⊢
    have h := comm_variants hu hv ht
    unfold sameIntertwiner
    split_ifs
    · exact h.1
    · exact h.2
  · simp only [show zsign k (1 : ZMod 2) = -1 by simp [zsign], neg_one_smul] at hu hv ht ⊢
    have h := anticomm_variants hu hv ht
    unfold sameIntertwiner
    split_ifs
    · exact h.1
    · exact h.2

theorem cl_interchange_of_eq {t t' : List I} (l m v : List I) (g h : Shape I)
    (ht : t = l ++ g.dom ++ m ++ h.dom ++ v) (ht' : t' = l ++ g.cod ++ m ++ h.cod ++ v) {p q : ℕ}
    (hp : l.length = p) (hq : (l ++ g.dom ++ m).length = q)
    (h₁ : SChain t (pl t [PG.ofShape g p, PG.ofShape h q]) t')
    (h₂ : SChain t (pl t [PG.ofShape h q, PG.ofShape g p]) t') :
    cl D Sc t t' [PG.ofShape g p, PG.ofShape h q] h₁ =
      zsign k (g.parity D * h.parity D) • cl D Sc t t' [PG.ofShape h q, PG.ofShape g p] h₂ := by
  subst ht ht' hp hq
  exact cl_interchange D Sc l m v g h h₁ h₂

theorem sChain_dotAny (t : List I) (b : ℕ) : SChain t (pl t [.dot b]) t := by
  simpa [tgt, PG.act] using sChain_pl t [.dot b]

/-- KKO (8.11) for `b < a`: a dot to the left of the pair passes through `g` with the sign
`(-1)^{p(ν_b)p(ν_a)p(ν_{a+1})}`. -/
theorem dot_left_comp_intertwinerHom (l₁ l₂ r : List I) (x i j : I) :
    dotE D Sc (l₁ ++ [x] ++ l₂ ++ [i, j] ++ r) l₁.length ≫
        intertwinerHom D Sc (l₁ ++ [x] ++ l₂) r i j =
      zsign k (D.parity x * (D.parity i * D.parity j)) •
        (intertwinerHom D Sc (l₁ ++ [x] ++ l₂) r i j ≫
          dotE D Sc (l₁ ++ [x] ++ l₂ ++ [j, i] ++ r) l₁.length) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, ← End.mul_def, ← End.mul_def, parity_sq]
    refine sameIntertwiner_mul_of D Sc _ ?_ ?_ ?_
    · have := genE_interchange D Sc l₁ l₂ ([i] ++ r) (.dot x) (.dot i) rfl rfl
        (w := l₁ ++ [x] ++ l₂ ++ [i, i] ++ r) (by simp [Shape.dom]) (p := l₁.length)
        (q := (l₁ ++ [x] ++ l₂).length) rfl (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape] using this
    · have := genE_interchange D Sc l₁ (l₂ ++ [i]) r (.dot x) (.dot i) rfl rfl
        (w := l₁ ++ [x] ++ l₂ ++ [i, i] ++ r) (by simp [Shape.dom]) (p := l₁.length)
        (q := (l₁ ++ [x] ++ l₂).length + 1) rfl (by simp [Shape.dom]; omega)
      simpa only [Shape.parity, PG.ofShape] using this
    · have := genE_interchange D Sc l₁ l₂ r (.dot x) (.cross i i) rfl rfl
        (w := l₁ ++ [x] ++ l₂ ++ [i, i] ++ r) (by simp [Shape.dom]) (p := l₁.length)
        (q := (l₁ ++ [x] ++ l₂).length) rfl (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape, parity_sq] using this
  · rw [intertwinerHom_of_ne D Sc _ r h, dotE_eq_cl D Sc (sChain_dotAny _ _),
      dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
    exact cl_interchange D Sc l₁ l₂ r (.dot x) (.cross i j) _ _

/-- KKO (8.11) for `b > a + 1`: a dot to the right of the pair passes through `g` with the sign
`(-1)^{p(ν_b)p(ν_a)p(ν_{a+1})}`. -/
theorem dot_right_comp_intertwinerHom (l m v : List I) (x i j : I) :
    dotE D Sc (l ++ [i, j] ++ (m ++ [x] ++ v)) (l ++ [i, j] ++ m).length ≫
        intertwinerHom D Sc l (m ++ [x] ++ v) i j =
      zsign k (D.parity x * (D.parity i * D.parity j)) •
        (intertwinerHom D Sc l (m ++ [x] ++ v) i j ≫
          dotE D Sc (l ++ [j, i] ++ (m ++ [x] ++ v)) (l ++ [i, j] ++ m).length) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, ← End.mul_def, ← End.mul_def, parity_sq]
    have flip : ∀ {f Y : End ((pres D Sc).obj (ob D (l ++ [i, i] ++ (m ++ [x] ++ v))))}
        {q : ZMod 2}, Y * f = zsign k q • (f * Y) → f * Y = zsign k q • (Y * f) := by
      intro f Y q hfy
      rw [hfy, smul_smul, zsign_mul_self, one_smul]
    refine sameIntertwiner_mul_of D Sc _ (flip ?_) (flip ?_) (flip ?_)
    · have := genE_interchange D Sc l ([i] ++ m) v (.dot i) (.dot x) rfl rfl
        (w := l ++ [i, i] ++ (m ++ [x] ++ v)) (by simp [Shape.dom]) (p := l.length)
        (q := (l ++ [i, i] ++ m).length) rfl (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape, mul_comm (D.parity i)] using this
    · have := genE_interchange D Sc (l ++ [i]) m v (.dot i) (.dot x) rfl rfl
        (w := l ++ [i, i] ++ (m ++ [x] ++ v)) (by simp [Shape.dom]) (p := l.length + 1)
        (q := (l ++ [i, i] ++ m).length) (by simp) (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape, mul_comm (D.parity i)] using this
    · have := genE_interchange D Sc l m v (.cross i i) (.dot x) rfl rfl
        (w := l ++ [i, i] ++ (m ++ [x] ++ v)) (by simp [Shape.dom]) (p := l.length)
        (q := (l ++ [i, i] ++ m).length) rfl (by simp [Shape.dom])
      simpa only [Shape.parity, PG.ofShape, parity_sq, mul_comm (D.parity i)] using this
  · rw [intertwinerHom_of_ne D Sc l _ h, dotE_eq_cl D Sc (sChain_dotAny _ _),
      dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp, cl_comp]
    have hs := cl_interchange_of_eq D Sc l m v (.cross i j) (.dot x)
      (t := l ++ [i, j] ++ (m ++ [x] ++ v)) (t' := l ++ [j, i] ++ (m ++ [x] ++ v))
      (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl
      (sChain_append_of (sChain_crossAt l _ i j) (sChain_dotAny _ _))
      (sChain_append_of (sChain_dotAny _ _) (sChain_crossAt l _ i j))
    have h' := congrArg (zsign k (D.parity x * (D.parity i * D.parity j)) • ·) hs
    simp only [smul_smul, Shape.parity, mul_comm (D.parity i * D.parity j), zsign_mul_self,
      one_smul] at h'
    exact h'.symm

/-! ### Dots through the moving-strand map -/

/-- A dot to the left of the moving strand passes through `g_n ⋯ g_1` with the sign
`(-1)^{p(ν_b) p(i) p(ν)}`. -/
theorem dot_left_comp_moveHom (i x : I) (l₁ : List I) (ν : List I) :
    ∀ (l l₂ : List I), l = l₁ ++ [x] ++ l₂ →
      dotE D Sc (l ++ i :: ν) l₁.length ≫ moveHom D Sc i l ν =
        zsign k (D.parity x * (D.parity i * wordSumParity D ν)) •
          (moveHom D Sc i l ν ≫ dotE D Sc (l ++ ν ++ [i]) l₁.length) := by
  induction ν with
  | nil =>
    intro l l₂ _
    simp only [moveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul]
    exact dotE_comp_eqToHom D Sc (by simp) _
  | cons j ν ih =>
    intro l l₂ hl
    subst hl
    simp only [moveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l₁ ++ [x] ++ l₂ ++ i :: j :: ν = l₁ ++ [x] ++ l₂ ++ [i, j] ++ ν by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_left_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc
        (show l₁ ++ [x] ++ l₂ ++ [j, i] ++ ν = (l₁ ++ [x] ++ l₂ ++ [j]) ++ i :: ν by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _),
      ih (l₁ ++ [x] ++ l₂ ++ [j]) (l₂ ++ [j]) (by simp), Linear.smul_comp, Category.assoc,
      dotE_comp_eqToHom D Sc
        (show l₁ ++ [x] ++ l₂ ++ [j] ++ ν ++ [i] = l₁ ++ [x] ++ l₂ ++ j :: ν ++ [i] by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq]

/-- KKO (8.13), first identity, for dots: the dot on the strand `ν_b` passes through
`g_n ⋯ g_1` from position `b + 1` to position `b`, with the sign `(-1)^{p(ν_b) p(i) p(ν)}`. -/
theorem dot_mem_comp_moveHom (i x : I) (v : List I) (m : List I) :
    ∀ (l ν : List I), ν = m ++ [x] ++ v →
      dotE D Sc (l ++ i :: ν) (l.length + 1 + m.length) ≫ moveHom D Sc i l ν =
        zsign k (D.parity x * (D.parity i * wordSumParity D ν)) •
          (moveHom D Sc i l ν ≫ dotE D Sc (l ++ ν ++ [i]) (l.length + m.length)) := by
  induction m with
  | nil =>
    intro l ν hν
    obtain rfl : ν = x :: v := by simp [hν]
    simp only [moveHom, List.length_nil, add_zero]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l ++ i :: x :: v = l ++ [i, x] ++ v by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_succ_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc (show l ++ [x, i] ++ v = (l ++ [x]) ++ i :: v by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dot_left_comp_moveHom D Sc i x l v (l ++ [x]) [] (by simp), Linear.smul_comp,
      Category.assoc,
      dotE_comp_eqToHom D Sc (show l ++ [x] ++ v ++ [i] = l ++ x :: v ++ [i] by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, ← zsign_add_eq]
    congr 2
    simp only [wordSumParity, List.map_cons, List.sum_cons]
    linear_combination (-D.parity i) * parity_sq (D.parity x)
  | cons j m ih =>
    intro l ν hν
    obtain rfl : ν = j :: (m ++ [x] ++ v) := by simp [hν]
    simp only [moveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l ++ i :: j :: (m ++ [x] ++ v) = l ++ [i, j] ++ (m ++ [x] ++ v) by simp),
      show l.length + 1 + (j :: m).length = (l ++ [i, j] ++ m).length by simp; omega,
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_right_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc
        (show l ++ [j, i] ++ (m ++ [x] ++ v) = (l ++ [j]) ++ i :: (m ++ [x] ++ v) by simp),
      Category.assoc,
      show (l ++ [i, j] ++ m).length = (l ++ [j]).length + 1 + m.length by simp; omega,
      ← Category.assoc (dotE D Sc _ _), ih (l ++ [j]) _ rfl, Linear.smul_comp, Category.assoc,
      show (l ++ [j]).length + m.length = l.length + (j :: m).length by simp; omega,
      dotE_comp_eqToHom D Sc (show l ++ [j] ++ (m ++ [x] ++ v) ++ [i] =
        l ++ j :: (m ++ [x] ++ v) ++ [i] by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq]

end OddMath.QuiverHecke
end

end

section

/-!
# Signed polynomial transport through an intertwiner chain

The ordinary-polynomial part of `DeformedProjectiveResolution.md`, §1,
used by the proposed QP induction in `DeformedGlobalQP.md`, §3. The
underlying dot identities are KKO I, arXiv:1206.5933v2, (8.13).

Every polynomial in the moving dot or an old strand dot transports through
the actual `moveHom`, by substituting the appropriate signed dot. No
polynomial parity or monicity hypothesis is required. Coefficients here
are in the purely even commutative ground ring. This does not transport
odd ELV coefficients or construct the balanced QP induction.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private theorem signed_pow_comp {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A B : C} (x : End A) (y : End B) (g : A ⟶ B) (p : ZMod 2)
    (h : x ≫ g = SKM.zsign k p • (g ≫ y)) (m : ℕ) :
    (x ^ m : End A) ≫ g = SKM.zsign k (m • p) • (g ≫ (y ^ m : End B)) := by
  induction m with
  | zero => simp [End.one_def, SKM.zsign]
  | succ m ih =>
    rw [pow_succ, End.mul_def, Category.assoc, ih, Linear.comp_smul,
      ← Category.assoc, h, Linear.smul_comp, smul_smul, ← zsign_add_eq,
      pow_succ, End.mul_def, succ_nsmul, Category.assoc]

/-- The moving-strand dot transport, for every exponent including zero. -/
theorem dot_pow_comp_moveHom (i : I) (l ν : List I) (m : ℕ) :
    (dotE D Sc (l ++ i :: ν) l.length ^ m : End _) ≫ moveHom D Sc i l ν =
      SKM.zsign k (m • (D.parity i * wordSumParity D ν)) •
        (moveHom D Sc i l ν ≫
          (dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length) ^ m : End _)) := by
  exact signed_pow_comp _ _ _ _ (dot_comp_moveHom D Sc i l ν) m

end OddMath.QuiverHecke
end

end

section

/-!
# An asymmetric odd Cartan quadratic requires a parameter comparison

For the symmetrizable all-odd datum with off-diagonal entries -2 and -4,
the homogeneous polynomial is `u²+v⁴`. Signed right multiplication changes
the signs of dot squares but not fourth powers. No common scalar on the
quadratic polynomial absorbs that discrepancy. This excludes only the
fixed-dot, unchanged-parameter scalar-crossing prescription, not an action
with transported parameters.
-/
namespace OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
open SKM SKM.SerrePolynomial

/-- Both vertices are odd; the off-diagonal exponents differ. -/
def datum : Datum Bool (Bool → ℤ) where
  cd := {
    root := fun j i => if i = j then 2 else if i then -4 else -2
    coroot := fun i => LinearMap.proj i
    coroot_root_self := fun i => by simp }
  isGCM := {
    diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j hij
      cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
    zero_comm := by
      intro i j
      cases i <;> cases j <;> norm_num [CartanDatum.cartanMatrix_apply] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else if i then -4 else -2)
    cases i <;> cases j <;> norm_num [even_iff_two_dvd]

/-- Positive symmetrizer `(2,1)`. -/
def symmetrizer : Symmetrizer datum where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

def scalars : Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

theorem homogeneous : scalars.Homogeneous := by
  intro _ _ _ _ _ _ _ h
  exact (h rfl).elim

theorem quadratic (u v : ℚ) :
    quadraticValue scalars false true u v = u ^ 2 + v ^ 4 := by
  have h₂ : datum.dn false true = 2 := rfl
  have h₄ : datum.dn true false = 4 := rfl
  simp [quadraticValue, scalars, h₂, h₄]

/-- The parameter family required by the mixed-square calculation. -/
def transportedScalars : Scalars datum ℚ where
  t := fun i j => if i = j then 1 else if i then -1 else 1
  t_self := by intro i; simp
  t_symm_of_d_eq_zero := by
    intro i j h
    have hz : datum.d i j ≠ 0 := by
      cases i <;> cases j <;> decide
    exact (hz h).elim
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

theorem transported_homogeneous : transportedScalars.Homogeneous := by
  intro _ _ _ _ _ _ _ h
  exact (h rfl).elim

/-- In square coordinates, no crossing-product scalar repairs unchanged parameters. -/
theorem no_common_quadratic_scalar :
    ¬ ∃ c : ℚ, ∀ z w : ℚ, c * (z + w ^ 2) = -z + w ^ 2 := by
  rintro ⟨c, hc⟩
  have h₁ := hc 1 0
  have h₂ := hc 0 1
  norm_num at h₁ h₂
  linarith

/-- Four signed odd right multiplications have positive sign. -/
theorem oddRight_fourth {A : Type*} [Ring A] (σ : A →+* A)
    (hσ : Function.Involutive σ) (y : A) (hy : σ y = -y) (h : A) :
    oddRight σ y (oddRight σ y (oddRight σ y (oddRight σ y h))) = h * y ^ 4 := by
  rw [oddRight_comp σ hσ y y hy, oddRight_comp σ hσ y y hy]
  noncomm_ring

/-- The signed right-multiplier mixed square passes after changing the quartic parameter.
This is an algebraic relation transfer, not an induced-projective functor. -/
theorem transported_mixed_square {A : Type*} [Ring A] (σ : A →+* A)
    (hσ : Function.Involutive σ) (x y u v : A)
    (hx : σ x = -x) (hy : σ y = -y) (hv : σ v = -v)
    (hquad : v * u = x * x - y ^ 4) (h : A) :
    -oddRight σ u (-oddRight σ v h) =
      oddRight σ x (oddRight σ x h) +
        oddRight σ y (oddRight σ y (oddRight σ y (oddRight σ y h))) := by
  rw [neg_oddRight_comp σ hσ u v hv, oddRight_comp σ hσ x x hx,
    oddRight_fourth σ hσ y hy, hquad]
  noncomm_ring

#print axioms homogeneous
#print axioms transported_mixed_square
#print axioms quadratic
#print axioms no_common_quadratic_scalar

end OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

end
