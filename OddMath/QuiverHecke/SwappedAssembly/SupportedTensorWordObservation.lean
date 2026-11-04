import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorObservationLinearity

/-! # Word-indexed supported tensor quotient observation

SwappedVacuumCoordinates §§3–7: the canonical actual matrix observation
is indexed by the stated target word through its proved literal colour
identity. All whole source maps and original weights are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The source quotient retains its exact target-word equality transport. -/
def tensorTargetWordQuotientEquiv (s : List I) {t r : List I} (h : t = r) :
    ((coefficientObj D Sc s ⟶ coefficientObj D Sc t) ⧸
      PowerWordQuotientCoordinates.kernel D Sc cutoff L s t) ≃ₗ[k]
    ((coefficientObj D Sc s ⟶ coefficientObj D Sc r) ⧸
      PowerWordQuotientCoordinates.kernel D Sc cutoff L s r) := by
  subst r
  exact LinearEquiv.refl k _

variable [Fintype I] (m : I → ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s t : List I)
local notation "N" => PowerWordContent.powerBound D cutoff L

/-- The canonical source-unit observation with its literal target labels
read as the specified target word. No generator comparison is supplied. -/
def tensorWordQuotientObservation
    (p : SPath (tensorSourceLabels D ΛP ΛR t) (0,tensorSourceContent D ΛP ΛR s) (0,0)) :
    tensorWordMatrixModule D Sc m cutoff ΛP ΛR L s t →ₗ[k]
      ((coefficientObj D Sc s ⟶ coefficientObj D Sc t) ⧸
        PowerWordQuotientCoordinates.kernel D Sc cutoff L s t) :=
  (tensorTargetWordQuotientEquiv D Sc cutoff L s (tensorSourceLabels_colors D ΛP ΛR t)).toLinearMap.comp
    (tensorMatrixQuotientObservationLinear D Sc m cutoff ΛP ΛR L hP hR s
      (a := SKM.ob D (ΛP - ΛR) (upWord t)) (tensorWordVacuumEndpoint D ΛP ΛR t) p
      (tensorSourceLabels_up D ΛP ΛR t))

/-- The word-indexed observation is the same canonical observation followed
only by its proved target-label quotient transport. -/
theorem tensorWordQuotientObservation_apply
    (p : SPath (tensorSourceLabels D ΛP ΛR t) (0,tensorSourceContent D ΛP ΛR s) (0,0))
    (x : tensorWordMatrixModule D Sc m cutoff ΛP ΛR L s t) :
    tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s t p x =
      tensorTargetWordQuotientEquiv D Sc cutoff L s (tensorSourceLabels_colors D ΛP ΛR t)
        (tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s
          (a := SKM.ob D (ΛP - ΛR) (upWord t)) (tensorWordVacuumEndpoint D ΛP ΛR t) p
          (tensorSourceLabels_up D ΛP ΛR t) x) := rfl

/-- The whole upward-path observation is independent of the chosen path
presentation; the exact original source sector determines that path. -/
theorem tensorWordQuotientObservation_path_independent
    (p q : SPath (tensorSourceLabels D ΛP ΛR t) (0,tensorSourceContent D ΛP ΛR s) (0,0)) :
    tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s t p =
      tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s t q := by
  have hpq : p = q := (SPath.subsingleton_of_upward_probe_zero
    (tensorSourceLabels_up D ΛP ΛR t) rfl).elim _ _
  cases hpq
  rfl

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
