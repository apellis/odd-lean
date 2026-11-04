import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorMatrixCoefficientObservation
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorWordObservation
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorVacuumObservation

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
  rfl

private theorem coefficient_coordinate_reindex (s t r : List I) (h : t = r) (Λ x : X)
    (hβ : blockWeight D Λ (s.reverse : Multiset I) = x)
    (A : ELVWeightProduct D Tw cutoff N Λ x)
    (e : A ≅ PowerWordWeight.wordFamily D Tw cutoff L Λ x t.reverse)
    (z : (A ⟨s.reverse,hβ⟩).obj
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
    (a : SYM D k) :
    let e' := e ≪≫ eqToIso (congrArg (PowerWordWeight.wordFamily D Tw cutoff L Λ x)
      (congrArg List.reverse h))
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

private theorem coefficient_coordinate_unit_class (s t : List I) (h : t = s) (Λ x : X)
    (hβ : blockWeight D Λ (s.reverse : Multiset I) = x)
    (A : ELVWeightProduct D Tw cutoff N Λ x)
    (e : A ≅ PowerWordWeight.wordFamily D Tw cutoff L Λ x t.reverse)
    (z : (A ⟨s.reverse,hβ⟩).obj
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
    (a : SYM D k)
    (hUnit :
      ((((e ≪≫ eqToIso (congrArg (PowerWordWeight.wordFamily D Tw cutoff L Λ x)
        (congrArg List.reverse h))).hom ⟨s.reverse,hβ⟩).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)) z) =
      PowerWordYoneda.unitVector D Tw cutoff L s.reverse) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s h
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t
        ((tensorWordCoefficientArrow D Sc cutoff Λ L x t.reverse a ⟨s.reverse,hβ⟩).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
          (((e.hom ⟨s.reverse,hβ⟩).total
            (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)) z))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) := by
  have hcoord := coefficient_coordinate_reindex D Sc cutoff L s t s h Λ x hβ A e z a
  change _ = PowerWordQuotientCoordinates.coordinate D Sc cutoff L s s
    ((tensorWordCoefficientArrow D Sc cutoff Λ L x s.reverse a ⟨s.reverse,hβ⟩).total
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
      _) at hcoord
  rw [hUnit] at hcoord
  apply hcoord.trans
  rw [wordCoefficientArrow_total]
  exact PowerWordQuotientCoordinates.coefficient_unit_class D Sc cutoff L s a

variable (m : I → ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "pS" => tensorSourcePath D ΛP ΛR s
local notation "upS" => tensorSourceLabels_up D ΛP ΛR s
local notation "endS" => tensorWordVacuumEndpoint D ΛP ΛR s
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP
local notation "βS" => tensorSourceWordBlock D ΛP ΛR s
local notation "wS" => PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl

attribute [local irreducible] tensorPathValueChart tensorSourcePathValueChart tensorOriginalSourceUnit
  tensorOriginalWordEntry tensorOriginalRowSourceIso tensorSourceWordUnit tensorMatrixVacuum
  tensorMatrixCoefficientAction PowerWordQuotientCoordinates.coordinate

set_option diagnostics true in
/-- The coefficient class along an arbitrary upward source path presentation. -/
private theorem coefficient_class_of_path (l : List (Col I X))
    (hl : l.map (fun d => d.l.2) = s)
    (p : SPath l (0,cS) (0,0)) (hup : ∀ d ∈ l, d.l.1 = true)
    (z : (((TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup).obj R₀) βS).obj wS)
    (a : SYM D k)
    (hu : ((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup ≪≫
      eqToIso (congrArg (PowerWordWeight.wordFamily D Tw cutoff L ΛR
        (ReservoirWord.weight D ΛR cS)) (congrArg List.reverse hl))).hom βS).total wS z =
      PowerWordYoneda.unitVector D Tw cutoff L s.reverse) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s hl
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (l.map (fun d => d.l.2))
        ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
          (l.map (fun d => d.l.2)).reverse a βS).total wS
          (((tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup).hom βS).total wS z))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) := by
  exact coefficient_coordinate_unit_class D Sc cutoff L s (l.map (fun d => d.l.2)) hl ΛR
    (ReservoirWord.weight D ΛR cS) βS.2 _ (tensorPathValueChart D Sc m cutoff ΛP ΛR L p hup) z a hu

set_option diagnostics true in
/-- Variant through the path lemma. -/
private theorem coefficient_vacuum_via_path (a : SYM D k) :
    tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s s pS
      (tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L s
        (SKM.ob D (ΛP - ΛR) (upWord s)) a (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s)) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) := by
  have hu : _ = _ := tensorOriginalSourceUnit_wordValue D Sc m cutoff ΛP ΛR L hP hR s
  rw [tensorSourceWordUnit_formula] at hu
  rw [tensorWordQuotientObservation_apply,tensorMatrixCoefficient_observation,
    tensorOriginalWordEntry_vacuum]
  unfold tensorSourcePathValueChart at hu
  refine coefficient_class_of_path D Sc cutoff L m ΛP ΛR s
    (SKM.ob D (ΛP - ΛR) (upWord s)).word
    (tensorSourceLabels_colors D ΛP ΛR s :
      ((SKM.ob D (ΛP - ΛR) (upWord s)).word).map (fun d => d.l.2) = s)
    pS upS _ a ?_
  exact hu

set_option diagnostics true in
/-- The unchanged canonical observation of the full raw coefficient action
on the actual matrix vacuum is the prescribed source class of coefficient
times identity. This does not identify presentation bubbles with that action. -/
theorem tensorWordQuotientObservation_coefficient_vacuum (a : SYM D k) :
    tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s s pS
      (tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L s
        (SKM.ob D (ΛP - ΛR) (upWord s)) a (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s)) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) := by
  have hu : _ = _ := tensorOriginalSourceUnit_wordValue D Sc m cutoff ΛP ΛR L hP hR s
  rw [tensorSourceWordUnit_formula] at hu
  rw [tensorWordQuotientObservation_apply,tensorMatrixCoefficient_observation,
    tensorOriginalWordEntry_vacuum]
  unfold tensorSourcePathValueChart at hu
  delta tensorSourceWordBlock at hu ⊢
  exact coefficient_coordinate_unit_class D Sc cutoff L s _ (tensorSourceLabels_colors D ΛP ΛR s)
    ΛR _ _ _ (tensorPathValueChart D Sc m cutoff ΛP ΛR L pS upS) _ a hu

/-- The coefficient-one specialization is the canonical source identity class. -/
theorem tensorWordQuotientObservation_vacuum :
    tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s s pS
      (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc 1 (𝟙 _)) := by
  simpa only [map_one,Module.End.one_apply] using
    (tensorWordQuotientObservation_coefficient_vacuum D Sc cutoff L m ΛP ΛR hP hR s 1)
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
