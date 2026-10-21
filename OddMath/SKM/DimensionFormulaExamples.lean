/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.DimensionFormula
import OddMath.SKM.Theorem103Examples

/-!
# Consumers of the BE2 graded-dimension formula

Two odd colours, populated mixed boundaries and rational scalar parameters.
The unconditional checks exercise finite-dimensional coefficient pieces,
parity-preserving evaluation and homogeneous surjectivity. Formula consumers
retain the Nondegeneracy Conjecture as a named premise; no instance of it is
asserted or manufactured.
-/

noncomputable section
namespace OddMath.SKM.DimensionFormulaExamples
open CategoryTheory StringDiagrams CoveringQuantum
open CoveringQuantum.UDot.ContextualExchangeExamples
open CoveringQuantum.UDot.GenericTensor CoveringQuantum.UDot.GenericVerma.MixedGram
open Theorem103Examples

/-- Constant rational parameters for two orthogonal odd colours. -/
def scalars : Scalars twoOddDatum.toSKM ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

/-- Constant bubble units. -/
def cScalars : CScalars scalars where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [scalars]

theorem homogeneous : scalars.Homogeneous :=
  fun _ _ _ _ _ _ _ _ h => absurd rfl h

theorem locallyFinite : twoOddDatum.skmSymmetrizer.DegreeLocallyFinite :=
  fun _ => Set.toFinite _

/-- The four-strand mixed boundary has both odd colours. -/
def matchingChoice (ε : Bool) : MatchingBasisChoice (boundary ε) (boundary ε) :=
  (MatchingBasisChoice.nonempty _ _).some

/-- A representative is present: the mixed example is not an empty family. -/
theorem matchingChoice_nonempty (ε : Bool) : ((matchingChoice ε).members).Nonempty := by
  have hm : IsMatching₂ (boundary ε) (boundary ε) [] := ⟨trivial, rfl⟩
  obtain ⟨R, hR, hr, _⟩ := exists_strictReduced_equiv hm
  obtain ⟨S, hS, _⟩ := (matchingChoice ε).complete R hR hr
  exact ⟨S, hS⟩

/-- Both integer and parity gradings are checked on a populated word family. -/
theorem component_surjective (ε : Bool) (μ : Bool → ℤ) (n : ℤ) (p : ZMod 2) :
    Function.Surjective
      ((matchingChoice ε).componentExpansion twoOddDatum.skmSymmetrizer cScalars μ (n, p)) :=
  (matchingChoice ε).componentExpansion_surjective
    twoOddDatum.skmSymmetrizer cScalars μ homogeneous (n, p)

/-- Finite-dimensional abstract coefficients at every degree and both parities. -/
theorem coefficient_finite (n : ℤ) (p : ZMod 2) :
    FiniteDimensional ℚ (SYM.component twoOddDatum.skmSymmetrizer ℚ (n, p)) :=
  SYM.finiteDimensional_component twoOddDatum.skmSymmetrizer locallyFinite (n, p)

/-- Negative coefficient degrees vanish, at either parity sign. -/
theorem coefficient_negative (σ : ℚ) (n : ℤ) (hn : n < 0) :
    (symDimension twoOddDatum.skmSymmetrizer ℚ σ).coeff n = 0 :=
  symDimension_coeff_neg twoOddDatum.skmSymmetrizer ℚ σ n hn

/-- BE2 (dum) in a populated two-colour mixed example, for every weight and
both signs. The sole conjectural input is explicit. -/
theorem mixed_formula (hN : NondegeneracyConjecture cScalars) (ε : Bool)
    (μ : Bool → ℤ) (σ : ℚ) (hσ : σ ^ 2 = 1) :
    homDimension twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite
      μ (boundary ε) (boundary ε) σ =
      signLaurent σ hσ (sesquilinearForm twoOddDatum
        (algebraWord twoOddDatum μ (boundary ε)) (algebraWord twoOddDatum μ (boundary ε))) *
        symDimension twoOddDatum.skmSymmetrizer ℚ σ :=
  hom_dimension_eq_form_mul_sym twoOddDatum cScalars homogeneous locallyFinite
    hN μ (boundary ε) (boundary ε) rfl σ hσ

end OddMath.SKM.DimensionFormulaExamples
