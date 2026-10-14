/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.AltBraidRotation

/-!
# The alternative braid relation ([BE2] Prop 7.6)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Prop 7.6, for all
colours `i, j, k`, every weight and every parity, over arbitrary `Datum`, `Scalars` and
`CScalars`:

* `prop_7_6`: `altL i j k = altR i j k + altCorrection i j k μ`, where the correction is zero
  unless `i = j = k`;
* `prop_7_6_ne`: the two sides agree unless `i = j = k`;
* `prop_7_6_equal`: the case `i = j = k` with the two triple sums written out.

The second triple sum carries the sign `(-1)^{|i|(h + r + s)}`; the paper prints
`(-1)^{|i|(h + r + s + t)}`. The two differ for odd `i` (ERRATA [BE2] 2).
-/

noncomputable section
namespace OddMath.SKM.AltBraid
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

include cs in
/-- The case `i ≠ j` of [BE2] Prop 7.6: cancel the leftward crossings on either side of
`left_braid` with the inversion relations for `i ≠ j`. -/
theorem alt_ne_left (i j a : I) (μ : X) (hij : i ≠ j) :
    cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altL i j a) =
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altR i j a) := by
  let P := (sigmaL i j).map (whL [] [up a])
  let Q := (sigmaL i j).map (whL [up a] [])
  have hp : SChain [up j, dn i, up a] P [dn i, up j, up a] :=
    (sChain_sigmaL i j).wh [] [up a] rfl rfl
  have hq : SChain [up a, up j, dn i] Q [up a, dn i, up j] :=
    (sChain_sigmaL i j).wh [up a] [] rfl rfl
  have E := cl_step (D := D) (Sc := Sc) μ P Q [] []
    (left_braid cs i j a (wt D μ []) hij) hp hq
    (L := P ++ leftBraidL i j a ++ Q) (L' := P ++ leftBraidR i j a ++ Q)
    (by simp) (by simp)
  have eL : cl D Sc μ [up j, dn i, up a] [up a, dn i, up j]
      (P ++ leftBraidL i j a ++ Q) =
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altR i j a) := by
    apply cl_step μ [] (altR i j a) [] [up a]
      (cl_invNe₁ Sc i j (wt D μ [up a]) hij) (by rfl) (altR_chain i j a)
    · simp [P, Q, leftBraidL, altR, List.append_assoc]
    · simp
  have eR : cl D Sc μ [up j, dn i, up a] [up a, dn i, up j]
      (P ++ leftBraidR i j a ++ Q) =
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altL i j a) := by
    apply cl_step μ (altL i j a) [] [up a] []
      (cl_invNe₂ Sc i j (wt D μ []) hij) (altL_chain i j a) (by rfl)
    · simp [P, Q, leftBraidR, altL, List.append_assoc]
    · simp
  exact (eL.symm.trans (E.trans eR)).symm

include cs in
/-- The case `i = k ≠ j` of [BE2] Prop 7.6, for all weights and parities. -/
theorem alt_eq_left_eq (i j : I) (μ : X) (hij : i ≠ j) :
    cl D Sc μ [up j, dn i, up i] [up i, dn i, up j] (altL i j i) =
      cl D Sc μ [up j, dn i, up i] [up i, dn i, up j] (altR i j i) :=
  alt_ne_left cs i j i μ hij

/-- The right-hand side correction of [BE2] Prop 7.6: zero unless `i = j = k`, and then the two
triple sums, with signs `(-1)^{|i|(h + r + s + 1)}` and `(-1)^{|i|(h + r + s)}`. -/
def altCorrection (i j a : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up j, dn i, up a]) ⟶
      (pres D Sc).obj (ob D μ [up a, dn i, up j]) := by
  classical
  exact if h : i = j ∧ i = a then by
    obtain ⟨rfl, rfl⟩ := h
    exact altCorrectionR cs i μ + altCorrectionL cs i μ
  else 0

/-- [BE2] Prop 7.6, with the sign correction ERRATA [BE2] 2 in the second sum. -/
theorem prop_7_6 (i j a : I) (μ : X) :
    cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altL i j a) =
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altR i j a) +
        altCorrection cs i j a μ := by
  classical
  by_cases hij : i = j
  · subst j
    by_cases hia : i = a
    · subst a
      have hc : altCorrection cs i i i μ = altCorrectionR cs i μ +
          altCorrectionL cs i μ := by
        unfold altCorrection
        rw [dite_eq_left (show i = i ∧ i = i from ⟨rfl, rfl⟩)]
      rw [hc]
      exact (alt_equal cs i μ).trans (by abel)
    · simpa only [altCorrection, hia, and_false, dite_false, add_zero] using
        alt_ne_right (Sc := Sc) i i a μ hia
  · simpa only [altCorrection, hij, false_and, dite_false, add_zero] using
      alt_ne_left cs i j a μ hij

/-- [BE2] Prop 7.6 for `i = j = k`, with both triple sums written out. -/
theorem prop_7_6_equal (i : I) (μ : X) :
    cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altL i i i) =
      cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altR i i i) +
        (∑ r ∈ range (D.h i μ + 1).toNat, ∑ s ∈ range (D.h i μ + 1).toNat,
          ∑ t ∈ range (D.h i μ + 1).toNat,
            isg k (D.parity i) (D.h i μ + r + s + 1) • altTermR cs i μ r s t) +
        (∑ r ∈ range (-D.h i μ - 1).toNat, ∑ s ∈ range (-D.h i μ - 1).toNat,
          ∑ t ∈ range (-D.h i μ - 1).toNat,
            isg k (D.parity i) (D.h i μ + r + s) • altTermL cs i μ r s t) :=
  alt_equal cs i μ

include cs in
/-- [BE2] Prop 7.6 when the three colours are not all equal: no correction. -/
theorem prop_7_6_ne (i j a : I) (μ : X) (h : ¬(i = j ∧ i = a)) :
    cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altL i j a) =
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altR i j a) := by
  classical
  simpa only [altCorrection, h, dite_false, add_zero] using prop_7_6 cs i j a μ

end OddMath.SKM.AltBraid
