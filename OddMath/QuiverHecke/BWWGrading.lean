/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.BWWPresentation
import OddMath.QuiverHecke.CoefficientGrading
import OddMath.SKM.BWWPresentation

/-!
# Gradings of the presentations with Brundan–Wang–Webster parameters

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2 (parameters over a graded ring);
J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1, "Gradings",
and the homogeneity condition (1.31).

* `QuiverHecke.isHomogeneous_coefficientGraded_presBWW`: if `tᵢⱼ` has degree `0` and every
  nonzero coefficient `cᵢⱼ(p, q)` of the box has its coefficient degree
  `2(dᵢdᵢⱼ - dᵢp - dⱼq)`, every relation of `QuiverHecke.presBWW` lies in one degree for the
  coefficient grading. Here the pure monomials, of positive coefficient degree
  (`SKM.coefficientDegree_pos_of_pure`), are allowed.
* Under (1.31) (`BWWScalars.Homogeneous`) both presentations are graded by `gdeg`
  (`QuiverHecke.isHomogeneous_gdeg_presBWW`, `SKM.isHomogeneous_gdeg_presBWW`), since then
  they are the Brundan–Ellis presentations.
-/

noncomputable section

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {k : Type w} [CommRing k]

/-- Homogeneous Brundan–Wang–Webster parameters give homogeneous Brundan–Ellis parameters. -/
theorem BWWScalars.Homogeneous.toScalars_homogeneous {P : BWWScalars D k}
    (hh : P.Homogeneous) : P.toScalars.Homogeneous :=
  (ScalarData.toBWW_homogeneous_iff P.toScalars).mp (by rw [BWWScalars.toScalars_toBWW]; exact hh)

variable (D) (sy : Symmetrizer D)

/-- Under (1.31), the Kac–Moody presentation with Brundan–Wang–Webster parameters is graded
by `gdeg`. -/
theorem isHomogeneous_gdeg_presBWW {P : BWWScalars D k} (hh : P.Homogeneous) :
    (presBWW D P).IsHomogeneous (gdeg D sy) := by
  rw [presBWW_eq_pres]
  exact isHomogeneous_gdeg D sy P.toScalars hh.toScalars_homogeneous

end OddMath.SKM

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams LinDiagram OddMath.Diagrams
open SKM (zsign dn_cast')

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {K : Type*} [CommRing K] {k : Type w} [CommRing k] [Algebra K k]
  (sy : SKM.Symmetrizer D) (𝒜 : ℤ → Submodule K k) [SetLike.GradedMonoid 𝒜]

/-- **Graded Brundan–Wang–Webster parameters.** If the `tᵢⱼ` have degree `0` and every
nonzero coefficient `cᵢⱼ(p, q)` of the box has its coefficient degree, every defining relation
of `presBWW` lies in one degree for the coefficient grading. -/
theorem isHomogeneous_coefficientGraded_presBWW (P : SKM.BWWScalars D k)
    (ht : ∀ i j, ((P.t i j : kˣ) : k) ∈ 𝒜 0)
    (hc : ∀ i j (p q : ℕ), i ≠ j → p ≤ D.dn i j → q ≤ D.dn j i → P.c i j p q ≠ 0 →
      P.c i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q)) :
    CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (presBWW D P) := by
  have hs : ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
      P.toScalars.s i j p q ≠ 0 →
        P.toScalars.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q) := by
    intro i j p q hij hp hq h0
    have h1 := dn_cast' (D := D) hij
    have h2 := dn_cast' (D := D) (Ne.symm hij)
    exact hc i j p q hij (by omega) (by omega) h0
  intro r
  cases r with
  | quadNe i j hij hd =>
    refine ⟨2 * (sy.d i * D.d i j), sub_mem (dg_mem_part D sy 𝒜 ?_)
      (sum_mem fun p hp => sum_mem fun q hq => ?_)⟩
    · rw [gsum_append, gsum_crossL, gsum_crossL]; have := sy.symm i j; linarith
    · by_cases h0 : P.c i j p q = 0
      · rw [h0, zero_smul]; exact zero_mem _
      · rw [Finset.mem_range] at hp hq
        refine smul_dg_mem_part D sy 𝒜 (hc i j p q hij (by omega) (by omega) h0) ?_
        rw [gsum_append, gsum_dotsL, gsum_dotsL, SKM.coefficientDegree]; ring
  | braidEq i j hij =>
    have hji := sy.symm i j
    refine ⟨2 * (sy.d i * D.d i j) - 2 * sy.d i, sub_mem
      (sub_mem (dg_mem_part D sy 𝒜 ?_) (dg_mem_part D sy 𝒜 ?_))
      (sum_mem fun p hp => sum_mem fun q hq => sum_mem fun s hs' => ?_)⟩
    · simp only [gsum_append, gsum_crossL, D.d_self]; linarith
    · simp only [gsum_append, gsum_crossL, D.d_self]; linarith
    · by_cases hz : P.c i j p q = 0
      · rw [hz, mul_zero, zero_smul]; exact zero_mem _
      · rw [Finset.mem_range] at hp hq hs'
        refine smul_dg_mem_part D sy 𝒜
          (SetLike.GradedMul.mul_mem (zsign_mem _) (hc i j p q hij (by omega) (by omega) hz)) ?_
        rw [gsum_append, gsum_append, gsum_dotsL, gsum_dotsL, gsum_dotsL, Nat.cast_sub (by omega),
          Nat.cast_sub (by omega), SKM.coefficientDegree]
        push_cast; ring
  | _ => exact isHomogeneous_coefficientGraded D sy 𝒜 P.toScalars ht hs _

/-- Under (1.31), the quiver Hecke presentation with Brundan–Wang–Webster parameters is graded
by `gdeg`. -/
theorem isHomogeneous_gdeg_presBWW {P : SKM.BWWScalars D k} (hh : P.Homogeneous) :
    (presBWW D P).IsHomogeneous (gdeg D sy) := by
  rw [← SKM.BWWScalars.toScalars_toBWW P, presBWW_toBWW]
  exact isHomogeneous_gdeg D sy P.toScalars hh.toScalars_homogeneous

end OddMath.QuiverHecke
