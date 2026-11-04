import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorMatrixCoefficientObservation

/-! # Raw source coefficient classes of the tensor matrix vacuum

SwappedVacuumCoordinates §§6–7: the canonical word observation of the
full raw coefficient action on the cyclic matrix vacuum is its prescribed
source coefficient-identity class. This does not attach presentation bubbles.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L

private theorem wordCoefficientArrow_total (Λ x : X) (ν ρ : List I)
    (hβ : blockWeight D Λ (ρ : Multiset I) = x) (a : SYM D k) :
    (tensorWordCoefficientArrow D Sc cutoff Λ L x ν a ⟨ρ,hβ⟩).total
      (PowerWordContentCyclicity.wordObject D Tw cutoff L ρ (ρ : Multiset I) rfl) =
    (coefficientModuleAction D Tw cutoff (powerWordModule D Tw cutoff L ν)
      (SYM.elvCoefficientQuotient D cutoff a)).total (OldCategory.mk ρ) := by
  change (PowerWordContentCross.contentWordArrow D Tw cutoff L (ρ : Multiset I) ν ν
    (coefficientEndomorphism D Tw cutoff ν (SYM.elvCoefficientQuotient D cutoff a))).total _ = _
  rw [PowerWordContentCross.contentWordArrow_total, ← PowerWordCoefficients.coefficient_fromArrow]

private theorem coefficient_coordinate_reindex (s t r : List I) (h : t = r) (Λ x : X)
    (hβ : blockWeight D Λ (s.reverse : Multiset I) = x)
    (A : ELVWeightProduct D Tw cutoff N Λ x)
    (e : A ≅ PowerWordWeight.wordFamily D Tw cutoff L Λ x t.reverse)
    (z : (A ⟨s.reverse,hβ⟩).obj
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
    (a : SYM D k) :
    let e' := e ≪≫ eqToIso (congrArg (fun ρ : List I =>
      PowerWordWeight.wordFamily D Tw cutoff L Λ x ρ.reverse) h)
    tensorTargetWordQuotientEquiv D Sc cutoff L s h
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t
        ((tensorWordCoefficientArrow D Sc cutoff Λ L x t.reverse a ⟨s.reverse,hβ⟩).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
          (((e.hom ⟨s.reverse,hβ⟩).total
            (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)) z))) =
      PowerWordQuotientCoordinates.coordinate D Sc cutoff L s r
        ((tensorWordCoefficientArrow D Sc cutoff Λ L x r.reverse a ⟨s.reverse,hβ⟩).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
          (((e'.hom ⟨s.reverse,hβ⟩).total
            (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)) z)) := by
  cases h
  simp only [tensorTargetWordQuotientEquiv, eqToIso_refl, Iso.trans_refl,
    LinearEquiv.refl_apply]
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
