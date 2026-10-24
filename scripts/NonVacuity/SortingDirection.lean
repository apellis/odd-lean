import OddMath.SKM.MixedCrossingLocalExamples

/-!
The source and target sorting components have opposite weight thresholds.
These identities use actual normalized left caps/cups. They do not assert
nonvanishing of a presented identity or prove matching independence.
-/

noncomputable section
namespace NonVacuity.SortingDirection
open CategoryTheory StringDiagrams Presentation OddMath.SKM

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- At negative weight one, the principal source component kills the left cap,
but the missing identity component pairs with it to a unit. -/
theorem source_boundary (cs : CScalars Sc) (i : I) (μ : X) (hh : D.h i μ = -1) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ epsP cs i μ = 0 ∧
    cl D Sc μ [] [dn i, up i] (etaL i 0) ≫ epsP cs i μ =
      (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ := by
  refine ⟨eq_2_14_a cs i μ (by omega), ?_⟩
  simpa [hh] using eq_2_14_c cs i μ 0 (by omega)

/-- The target-side counterpart occurs at positive weight one, not negative. -/
theorem target_boundary (cs : CScalars Sc) (i : I) (μ : X) (hh : D.h i μ = 1) :
    etaP cs i μ ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) = 0 ∧
    etaP cs i μ ≫ cl D Sc μ [up i, dn i] [] (epsL i 0) =
      (cs.c μ i : k) • 𝟙 _ := by
  refine ⟨eq_2_13_a cs i μ (by omega), ?_⟩
  simpa [hh] using eq_2_13_c cs i μ 0 (by omega)

/-- The zero-dot source cap is the normalized left cap, not a substituted
unrelated inverse component. -/
theorem source_cap_normalization (cs : CScalars Sc) (i : I) (μ : X)
    (hh : D.h i μ = -1) :
    epsP cs i μ = (↑(cs.c μ i)⁻¹ : k) • cl D Sc μ [dn i, up i] [] (dcapL i 0) := by
  simpa [hh] using epsP_of_neg cs (i := i) (μ := μ) (by omega)

private abbrev D₂ := MixedCrossingLocalExamples.oddDatum
private def sc : Scalars D₂ ℚ where
  t := fun _ _ => 1
  t_self := by intros; rfl
  t_symm_of_d_eq_zero := by intros; rfl
  s := fun _ _ _ _ => 0
  s_symm := by intros; rfl
  s_eq_zero := by intros; rfl
  two_isUnit := by intro _; exact isUnit_iff_ne_zero.mpr (by norm_num)

private def cs : CScalars sc where
  c := fun _ _ => 1
  shift := by intros; simp [sc]

private abbrev muNeg : Bool → ℤ := fun _ => -1
private abbrev muPos : Bool → ℤ := fun _ => 1

/-- Both components are instantiated over admissible odd rational data. -/
example :
    cl D₂ sc muNeg [up false, dn false] [dn false, up false] (sigmaL false false) ≫
        epsP cs false muNeg = 0 ∧
    cl D₂ sc muNeg [] [dn false, up false] (etaL false 0) ≫ epsP cs false muNeg = 𝟙 _ := by
  simpa [cs] using source_boundary cs false muNeg rfl

example :
    etaP cs false muPos ≫
        cl D₂ sc muPos [up false, dn false] [dn false, up false] (sigmaL false false) = 0 ∧
    etaP cs false muPos ≫ cl D₂ sc muPos [up false, dn false] [] (epsL false 0) = 𝟙 _ := by
  simpa [cs] using target_boundary cs false muPos rfl

example : epsP cs false muNeg = cl D₂ sc muNeg [dn false, up false] [] (dcapL false 0) := by
  simpa [cs] using source_cap_normalization cs false muNeg rfl

#print axioms source_boundary
#print axioms target_boundary
#print axioms source_cap_normalization
end NonVacuity.SortingDirection
