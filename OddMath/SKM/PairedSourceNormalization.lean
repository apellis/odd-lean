import OddMath.SKM.PairedSourceEvaluation

/-! Unit-triangular normalization from the actual left-leg cap serializer to
right-leg cap powers. The odd correction is retained over arbitrary rings. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Downward-dot cap powers are not generally equal to upward-dot powers.
Their difference is a strictly smaller cap row followed by a residual loop. -/
theorem source_cap_downward_triangular (cs : CScalars Sc) (i : I) (μ : X) (b : ℕ) :
    ∃ (a : k) (z : End ((pres D Sc).obj (ob D μ []))), IsUnit a ∧
      (b = 0 → z = 0) ∧
      cpow (dLM D Sc i μ) b ≫ epsP cs i μ =
        a • (cpow (uRM D Sc i μ) b ≫ epsP cs i μ) +
          cpow (uRM D Sc i μ) (b - 1) ≫ epsP cs i μ ≫ z := by
  rcases zmod2_cases (D.parity i) with hi | hi
  · refine ⟨1, 0, isUnit_one, fun _ => rfl, ?_⟩
    rw [Limits.comp_zero, Limits.comp_zero, add_zero, one_smul,
      lemma41_eq3_even cs i μ hi]
  · have H := lemma41_eq3_odd cs i μ hi b
    have unit_sign (q : ZMod 2) : IsUnit (zsign k q) :=
      IsUnit.of_mul_eq_one _ (zsign_mul_self q)
    by_cases hb : Even b
    · rw [ite_eq_left hb] at H
      refine ⟨zsign k ((b / 2 : ℕ) : ZMod 2), 0, unit_sign _, fun _ => rfl, ?_⟩
      rw [Limits.comp_zero, Limits.comp_zero, add_zero]
      exact H.symm
    · have hpos : 0 < b := by
        by_contra hn
        have hz : b = 0 := by omega
        exact hb (by simp [hz])
      have he : Even (b - 1) := by
        rw [Nat.even_iff] at hb ⊢
        omega
      have Hprev := lemma41_eq3_odd cs i μ hi (b - 1)
      rw [ite_eq_left he] at Hprev
      rw [ite_eq_right hb] at H
      let s := zsign k (D.h i μ : ZMod 2)
      let t := zsign k ((b / 2 : ℕ) : ZMod 2)
      let t' := zsign k (((b - 1) / 2 : ℕ) : ZMod 2)
      refine ⟨s * t, (-(s * 2 * t')) • oddBubble cs i μ,
        (unit_sign _).mul (unit_sign _), fun hz => by omega, ?_⟩
      have hs : s * s = 1 := zsign_mul_self _
      have HH := congrArg (fun f => s • f) H
      change s • (t • _) = s • (s • _ + (2 : k) • _) at HH
      rw [smul_add, smul_smul, smul_smul, hs, one_smul, smul_smul] at HH
      have HE : cpow (dLM D Sc i μ) (b - 1) ≫ epsP cs i μ =
          t' • (cpow (uRM D Sc i μ) (b - 1) ≫ epsP cs i μ) := Hprev.symm
      rw [← Category.assoc (cpow (dLM D Sc i μ) (b - 1)), HE,
        Linear.smul_comp, smul_smul] at HH
      rw [Linear.comp_smul, Linear.comp_smul, ← Category.assoc, neg_smul]
      exact eq_sub_of_add_eq HH.symm

#print axioms source_cap_downward_triangular
end OddMath.SKM
