/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerMeet

/-!
# Reverse all-equal intertwiner braid

The reverse-product form of Kang–Kashiwara–Oh Lemma 8.3 for the variants
from (8.8), in an arbitrary signed nilHecke block. Passing to the opposite
ring reverses the braid identity; the two-strand variants are op-invariant.
The categorical specialization includes both parities and arbitrary contexts.
-/

namespace OddMath.QuiverHecke.SignedNilHecke
variable {B : Type*} [Ring B]

/-- Reversing products preserves the signed nilHecke relations. -/
theorem IsSignedNilHeckeFamily.op {ε : ℤˣ} {s n : ℕ} {X T : ℕ → B}
    (hF : IsSignedNilHeckeFamily ε s n X T) :
    IsSignedNilHeckeFamily ε s n (fun j => MulOpposite.op (X j))
      (fun j => MulOpposite.op (T j)) where
  x_comm a b ha hb hc hd he := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_op] using
      hF.x_comm b a hc hd ha hb he.symm
  x_t_comm a j ha hb hc hd he hf := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_op]
    rw [hF.x_t_comm a j ha hb hc hd he hf, eps_smul_eps_smul]
  t_comm j l ha hb hc := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_op]
    rw [hF.t_comm j l ha hb hc, eps_smul_eps_smul]
  t_sq j ha hb := by
    apply MulOpposite.unop_injective
    simpa using hF.t_sq j ha hb
  braid j ha hb := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, ← mul_assoc] using hF.braid j ha hb
  t_x j ha hb := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_sub, MulOpposite.unop_smul,
      MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_one] using hF.x_t j ha hb
  x_t j ha hb := by
    apply MulOpposite.unop_injective
    simpa only [MulOpposite.unop_sub, MulOpposite.unop_smul,
      MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_one] using hF.t_x j ha hb

/-- The odd variant is unchanged by reversing products. -/
theorem OddTwo.unop_element {u v T : B} (h : OddTwo u v T) :
    MulOpposite.unop (OddNilHecke.Intertwiner.element
      (MulOpposite.op u) (MulOpposite.op v) (MulOpposite.op T)) =
      OddNilHecke.Intertwiner.element u v T := by
  simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff,
    MulOpposite.unop_mul, MulOpposite.unop_sub, MulOpposite.unop_op,
    pow_two, mul_sub, sub_mul, mul_assoc, h.tu', h.tv', h.vu, h.vu',
    mul_one, one_mul, mul_neg, neg_mul, neg_neg]
  noncomm_ring

/-- The even variant is unchanged by reversing products. -/
theorem EvenTwo.unop_gEven {u v T : B} (h : EvenTwo u v T) :
    MulOpposite.unop (gEven (MulOpposite.op u) (MulOpposite.op v) (MulOpposite.op T)) =
      gEven u v T := by
  simp only [gEven, phiEven, MulOpposite.unop_mul, MulOpposite.unop_sub,
    MulOpposite.unop_add, MulOpposite.unop_op,
    mul_add, add_mul, mul_sub, sub_mul, mul_assoc, h.tu', h.tv', h.vu,
    mul_one, one_mul]
  noncomm_ring

variable {s n : ℕ} {X T : ℕ → B}

/-- The reverse braid identity for the odd variants. -/
theorem IsSignedNilHeckeFamily.reverse_braid_element
    (hF : IsSignedNilHeckeFamily (-1) s n X T) {j : ℕ}
    (h₁ : s ≤ j) (h₂ : j + 2 < s + n) :
    OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j) *
        OddNilHecke.Intertwiner.element (X (j + 1)) (X (j + 2)) (T (j + 1)) * T j =
      T (j + 1) * (OddNilHecke.Intertwiner.element (X j) (X (j + 1)) (T j) *
        OddNilHecke.Intertwiner.element (X (j + 1)) (X (j + 2)) (T (j + 1))) := by
  have h := congrArg MulOpposite.unop (hF.op.braid_element h₁ h₂)
  simpa only [MulOpposite.unop_mul, MulOpposite.unop_op,
    (hF.oddTwo h₁ (by omega)).unop_element,
    (hF.oddTwo (j := j + 1) (by omega) (by omega)).unop_element] using h

/-- The reverse braid identity for the even variants. -/
theorem IsSignedNilHeckeFamily.reverse_braid_gEven
    (hF : IsSignedNilHeckeFamily 1 s n X T) {j : ℕ}
    (h₁ : s ≤ j) (h₂ : j + 2 < s + n) :
    gEven (X j) (X (j + 1)) (T j) *
        gEven (X (j + 1)) (X (j + 2)) (T (j + 1)) * T j =
      T (j + 1) * (gEven (X j) (X (j + 1)) (T j) *
        gEven (X (j + 1)) (X (j + 2)) (T (j + 1))) := by
  have h := congrArg MulOpposite.unop (hF.op.braid_gEven h₁ h₂)
  simpa only [MulOpposite.unop_mul, MulOpposite.unop_op,
    (hF.evenTwo h₁ (by omega)).unop_gEven,
    (hF.evenTwo (j := j + 1) (by omega) (by omega)).unop_gEven] using h

end OddMath.QuiverHecke.SignedNilHecke

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- Reverse chronological all-equal braid, in arbitrary prefix and suffix contexts.
This reverses products using the opposite signed nilHecke family, rather than
merely taking the symmetry of the forward meet identity. -/
theorem cross_comp_sameIntertwiner_sameIntertwiner (l v : List I) (i : I) :
    crossE D Sc (l ++ [i, i, i] ++ v) l.length ≫
      sameIntertwiner D Sc (l ++ [i, i, i] ++ v) (l.length + 1) i ≫
        sameIntertwiner D Sc (l ++ [i, i, i] ++ v) l.length i =
    sameIntertwiner D Sc (l ++ [i, i, i] ++ v) (l.length + 1) i ≫
      sameIntertwiner D Sc (l ++ [i, i, i] ++ v) l.length i ≫
        crossE D Sc (l ++ [i, i, i] ++ v) (l.length + 1) := by
  have hF : IsSignedNilHeckeFamily (zunit (D.parity i)) l.length 3
      (dotE D Sc (l ++ [i, i, i] ++ v)) (crossE D Sc (l ++ [i, i, i] ++ v)) :=
    isSignedNilHeckeFamily_block D Sc l v i 3
  rw [← Category.assoc, ← Category.assoc, ← End.mul_def, ← End.mul_def,
    ← End.mul_def, ← End.mul_def]
  by_cases hp : D.parity i = 1
  · rw [hp, show zunit (1 : ZMod 2) = -1 by simp [zunit]] at hF
    simp only [sameIntertwiner, hp, ite_true]
    simpa only [mul_assoc] using hF.reverse_braid_element (j := l.length) le_rfl (by omega)
  · have hp0 := parity_eq_zero_of_ne_one hp
    rw [hp0, show zunit (0 : ZMod 2) = 1 by simp [zunit]] at hF
    simp only [sameIntertwiner, hp, ite_false]
    simpa only [mul_assoc] using hF.reverse_braid_gEven (j := l.length) le_rfl (by omega)

end OddMath.QuiverHecke
