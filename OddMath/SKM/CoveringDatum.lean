/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.Datum
import OddMath.SKM.PositiveMatchingGrading

/-!
# Covering root data and positive matching degrees

The Cartan and weight data in [BE2, arXiv:1701.04133v2, §§1, 9] are shared by the
covering quantum group and the super Kac–Moody category. `RootDatum.toSKM` retains the
weight type, roots, coroots and parity; `RootDatum.skmSymmetrizer` casts the positive
natural symmetrizer to integers. In particular, the SKM parameter `dᵢⱼ` is `-aᵢⱼ`.

The degree table after (1.31) and the table preceding Theorem 10.3 then give crossing
degree `-Q.dot i j`, dot degree `2 * Q.d i`, and their respective parities
`Q.parity i * Q.parity j` and `Q.parity i`. The theorem
`positive_matching_covering_degree_parity` applies the existing positive matching
calculation to these data, supplying the crossing contribution needed in Claim 1.
The permutation is physical left-to-right bottom-to-top, as in
`positive_matching_degree_parity`; this does not change to the printed word convention.

Only an additive commutative weight group is needed, with no finiteness or bar-consistency
hypothesis. These are syntactic diagram degrees, not a new quotient grading. This module
does not compare forms, sum decorated diagrams, or prove independence of representatives.
-/

namespace OddMath.CoveringQuantum.RootDatum

open SKM

variable {I X : Type*} [AddCommGroup X] (Q : RootDatum I X)

/-- The same roots, coroots and parity, in the SKM convention of [BE2, §1]. -/
def toSKM : Datum I X where
  cd := Q.cd
  isGCM := by
    have h : Q.cd.cartanMatrix = Q.a := by
      ext i j
      exact Q.coroot_root i j
    rw [h]
    exact Q.isGCM
  parity := Q.parity
  even_of_odd := by
    intro i j hi
    rw [Q.coroot_root]
    exact Q.even_of_odd i j hi

@[simp] theorem toSKM_cd : Q.toSKM.cd = Q.cd := rfl

@[simp] theorem toSKM_α (i : I) : Q.toSKM.α i = Q.α i := rfl

@[simp] theorem toSKM_h (i : I) (μ : X) : Q.toSKM.h i μ = Q.h i μ := rfl

@[simp] theorem toSKM_parity (i : I) : Q.toSKM.parity i = Q.parity i := rfl

/-- [BE2, §1]: `dᵢⱼ = -aᵢⱼ`. -/
@[simp] theorem toSKM_d (i j : I) : Q.toSKM.d i j = -Q.a i j :=
  congrArg Neg.neg (Q.coroot_root i j)

/-- The positive integral symmetrizer from [BE2, §9], on the same SKM datum. -/
def skmSymmetrizer : Symmetrizer Q.toSKM where
  d i := Q.d i
  pos i := by exact_mod_cast Q.d_pos i
  symm i j := by
    simp only [toSKM_d, mul_neg]
    exact congrArg Neg.neg (Q.d_mul_symm i j)

@[simp] theorem skmSymmetrizer_d (i : I) : Q.skmSymmetrizer.d i = (Q.d i : ℤ) := rfl

/-- Crossing weights in the degree table preceding [BE2, Theorem 10.3]. -/
theorem skm_crossing_weight (i j : I) :
    Q.skmSymmetrizer.d i * Q.toSKM.d i j = -Q.toSuperCartanDatum.dot i j := by
  simp only [skmSymmetrizer_d, toSKM_d, mul_neg, SuperCartanDatum.dot]

@[simp] theorem gdeg_toSKM_cross (i j : I) (μ : X) :
    gdeg Q.toSKM Q.skmSymmetrizer (.cross i j, μ) =
      -Q.toSuperCartanDatum.dot i j :=
  Q.skm_crossing_weight i j

@[simp] theorem gdeg_toSKM_dot (i : I) (μ : X) :
    gdeg Q.toSKM Q.skmSymmetrizer (.dot i, μ) = 2 * (Q.d i : ℤ) := rfl

@[simp] theorem parity_toSKM_cross (i j : I) :
    Shape.parity Q.toSKM (.cross i j) = Q.parity i * Q.parity j := rfl

@[simp] theorem parity_toSKM_dot (i : I) :
    Shape.parity Q.toSKM (.dot i) = Q.parity i := rfl

end OddMath.CoveringQuantum.RootDatum

namespace OddMath.SKM

open StringDiagrams StringDiagrams.Chord
open scoped BigOperators

/-- The crossing contribution in [BE2, Theorem 10.3, proof of Claim 1], with degrees
expressed in the covering datum's bilinear form. The datum compatibility is derived from
`Q`, not assumed; `he` uses physical left-to-right bottom-to-top endpoints. -/
theorem positive_matching_covering_degree_parity {I X : Type*} [AddCommGroup X]
    (Q : CoveringQuantum.RootDatum I X) (μ : X)
    {n : ℕ} (a b : Fin n → I) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (e : Equiv.Perm (Fin n))
    (he : ∀ r, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (n - 1 - r.val) (n + (e r).val)) :
    ∃ (L : List (LayerData I))
      (hL : SChain (List.ofFn fun r => (true, a r)) L (List.ofFn fun r => (true, b r))),
      L.map ofL = tLay (List.ofFn fun r => (true, a r)) R ∧
      Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer) (mkD Q.toSKM μ L hL) =
        ∑ r, ∑ s with r < s ∧ e s < e r, -Q.toSuperCartanDatum.dot (a r) (a s) ∧
      xpar Q.toSKM μ (tLay (List.ofFn fun r => (true, a r)) R) =
        ∑ r, ∑ s with r < s ∧ e s < e r, Q.parity (a r) * Q.parity (a s) := by
  simpa only [CoveringQuantum.RootDatum.skm_crossing_weight,
    CoveringQuantum.RootDatum.toSKM_parity] using
    positive_matching_degree_parity Q.toSKM Q.skmSymmetrizer μ a b hR hred e he

end OddMath.SKM
