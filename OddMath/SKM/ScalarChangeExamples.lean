import OddMath.SKM.ScalarChangePresentation
import OddMath.SKM.MixedCrossingLocalExamples

/-! Brundan–Ellis Definition 1.5 and (1.17): parameters, presented Hom,
and normalized left adjunction under a noninjective odd specialization. -/

namespace OddMath.SKM.ScalarChangeExamples

open MixedCrossingLocalExamples ScalarChange

private def source : Scalars oddDatum (ZMod 9) where
  t _ _ := 1
  t_self _ := rfl
  t_symm_of_d_eq_zero _ _ _ := rfl
  s _ _ _ _ := 0
  s_symm _ _ _ _ := rfl
  s_eq_zero _ _ _ _ _ := rfl
  two_isUnit _ := (ZMod.isUnit_iff_coprime 2 9).2 (by decide)

private def bubble : CScalars source where
  c _ _ := 1
  shift _ _ _ := rfl

private def specialize : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) _

/-- Both odd colours retain their required invertible `2` after reduction. -/
theorem target_two_isUnit : IsUnit (2 : ZMod 3) :=
  (scalars oddDatum specialize source).two_isUnit ⟨false, rfl⟩

/-- The transported bubble units satisfy the weight-shift law. -/
theorem target_bubble_shift (μ : Bool → ℤ) (i j : Bool) :
    (cScalars oddDatum specialize bubble).c (μ + oddDatum.α j) i =
      (scalars oddDatum specialize source).t i j *
        (cScalars oddDatum specialize bubble).c μ i :=
  (cScalars oddDatum specialize bubble).shift μ i j

/-- This specialization kills a nonzero coefficient and is not a field-valued
embedding; consequently a proof via preserving independence cannot be used. -/
theorem specialization_kills_nonzero :
    (3 : ZMod 9) ≠ 0 ∧ specialize (3 : ZMod 9) = 0 := by
  constructor <;> decide

open CategoryTheory StringDiagrams

/-- The odd dot is preserved in the presented Hom quotient. -/
theorem odd_dot_specializes (μ : Bool → ℤ) (i : Bool) :
    homMap specialize oddDatum source _ _
        (cl oddDatum source μ [up i] [up i] (dotsL [] i [] 1)) =
      cl oddDatum (scalars oddDatum specialize source) μ [up i] [up i] (dotsL [] i [] 1) :=
  homMap_cl specialize oddDatum source _ _ _ _

/-- Noninjectivity is exercised on a scalar multiple of a presented odd dot,
not just on the parameter ring. No nonvanishing of that dot is assumed. -/
theorem three_times_odd_dot_specializes_to_zero (μ : Bool → ℤ) (i : Bool) :
    homMap specialize oddDatum source _ _
      ((3 : ZMod 9) • cl oddDatum source μ [up i] [up i] (dotsL [] i [] 1)) = 0 := by
  rw [homMap_smul, specialization_kills_nonzero.2, zero_smul]

/-- Every relation label specializes, including the same-colour inverse
matrices at positive, negative and zero heights. -/
theorem odd_relation_specializes (r : Rel oddDatum) :
    coeff specialize (relation oddDatum source r) =
      relation oddDatum (scalars oddDatum specialize source) r :=
  coeff_relation specialize oddDatum source r

/-- The mixed leftward crossing generator is unchanged in the quotient. -/
theorem mixed_inverse_specializes (μ : Bool → ℤ) :
    homMap specialize oddDatum source _ _
      (cl oddDatum source μ [dn false, up true] [up true, dn false]
        (lcrossL false true)) =
      cl oddDatum (scalars oddDatum specialize source) μ [dn false, up true]
        [up true, dn false] (lcrossL false true) :=
  homMap_cl specialize oddDatum source _ _ _ _

/-- Prescribed odd normalized cups and caps retain the supplied units. -/
theorem odd_left_adjunction_specializes (μ : Bool → ℤ) (i : Bool) :
    homMap specialize oddDatum source _ _ (etaP bubble i μ) =
        etaP (cScalars oddDatum specialize bubble) i μ ∧
      homMap specialize oddDatum source _ _ (epsP bubble i μ) =
        epsP (cScalars oddDatum specialize bubble) i μ :=
  ⟨homMap_etaP specialize oddDatum source bubble i μ,
    homMap_epsP specialize oddDatum source bubble i μ⟩

/-- The bundled functor fixes identities on nonempty odd boundary words. -/
theorem odd_identity_specializes (μ : Bool → ℤ) :
    (presentationFunctor specialize oddDatum source).map
        (𝟙 ((pres oddDatum source).obj (ob oddDatum μ [up false, dn true]))) =
      𝟙 _ :=
  (presentationFunctor specialize oddDatum source).map_id _

end OddMath.SKM.ScalarChangeExamples
