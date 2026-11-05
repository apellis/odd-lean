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
    (A : elvWeightSpace D Tw cutoff N Λ x)
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
    (A : elvWeightSpace D Tw cutoff N Λ x)
    (e : A ≅ PowerWordWeight.wordFamily D Tw cutoff L Λ x t.reverse)
    (z : (A ⟨s.reverse,hβ⟩).obj
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
    (a : SYM D k)
    (hUnit : @Eq ((PowerWordWeight.wordFamily D Tw cutoff L Λ x s.reverse ⟨s.reverse,hβ⟩).obj
        (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
      ((((e ≪≫ eqToIso (congrArg (PowerWordWeight.wordFamily D Tw cutoff L Λ x)
        (congrArg List.reverse h))).hom ⟨s.reverse,hβ⟩).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)) z)
      (PowerWordYoneda.unitVector D Tw cutoff L s.reverse)) :
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

private theorem coefficient_coordinate_unit_class_of_chart (s t : List I) (h : t = s) (Λ x : X)
    (hβ : blockWeight D Λ (s.reverse : Multiset I) = x)
    (A : elvWeightSpace D Tw cutoff N Λ x)
    (e : A ≅ PowerWordWeight.wordFamily D Tw cutoff L Λ x t.reverse)
    (e' : A ≅ PowerWordWeight.wordFamily D Tw cutoff L Λ x s.reverse)
    (he : e' = e ≪≫ eqToIso (congrArg (PowerWordWeight.wordFamily D Tw cutoff L Λ x)
      (congrArg List.reverse h)))
    (z : (A ⟨s.reverse,hβ⟩).obj
      (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
    (a : SYM D k)
    (hUnit : ((e'.hom ⟨s.reverse,hβ⟩).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)) z =
      PowerWordYoneda.unitVector D Tw cutoff L s.reverse) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s h
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t
        ((tensorWordCoefficientArrow D Sc cutoff Λ L x t.reverse a ⟨s.reverse,hβ⟩).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
          (((e.hom ⟨s.reverse,hβ⟩).total
            (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)) z))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) := by
  subst he
  exact coefficient_coordinate_unit_class D Sc cutoff L s t h Λ x hβ A e z a hUnit

private theorem coefficient_coordinate_unit_class_of_block (s t : List I) (h : t = s) (Λ x : X)
    (hβ : blockWeight D Λ (s.reverse : Multiset I) = x)
    (A : elvWeightSpace D Tw cutoff N Λ x)
    (e : A ≅ PowerWordWeight.wordFamily D Tw cutoff L Λ x t.reverse)
    (e' : A ≅ PowerWordWeight.wordFamily D Tw cutoff L Λ x s.reverse)
    (he : e' = e ≪≫ eqToIso (congrArg (PowerWordWeight.wordFamily D Tw cutoff L Λ x)
      (congrArg List.reverse h)))
    (z : (A ⟨s.reverse,hβ⟩).obj (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
    (a : SYM D k) (β : WeightBlocks D Λ x) (hβe : β = ⟨s.reverse,hβ⟩)
    (w : ContentCategory D Tw cutoff N β.1) (hw : HEq w (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl))
    (z' : (A β).obj w) (hz : HEq z' z)
    (u : (PowerWordWeight.wordFamily D Tw cutoff L Λ x s.reverse β).obj w)
    (hu : HEq u (PowerWordYoneda.unitVector D Tw cutoff L s.reverse))
    (hUnit : (e'.hom β).total w z' = u) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s h
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t
        ((tensorWordCoefficientArrow D Sc cutoff Λ L x t.reverse a ⟨s.reverse,hβ⟩).total
          (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)
          (((e.hom ⟨s.reverse,hβ⟩).total
            (PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl)) z))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) := by
  subst hβe
  obtain rfl := eq_of_heq hw
  obtain rfl := eq_of_heq hz
  obtain rfl := eq_of_heq hu
  exact coefficient_coordinate_unit_class_of_chart D Sc cutoff L s t h Λ x hβ A e e' he _ a hUnit

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

/-- The vacuum observation, read through its literal row chart. -/
private theorem coefficient_vacuum_unfold (a : SYM D k) :
    tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s s pS
      (tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L s
        (SKM.ob D (ΛP - ΛR) (upWord s)) a (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s)) =
    tensorTargetWordQuotientEquiv D Sc cutoff L s (tensorSourceLabels_colors D ΛP ΛR s)
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s ((SKM.ob D (ΛP - ΛR) (upWord s)).word.map (fun d => d.l.2))
        ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
          ((SKM.ob D (ΛP - ΛR) (upWord s)).word.map (fun d => d.l.2)).reverse a βS).total wS
          (((tensorPathValueChart D Sc m cutoff ΛP ΛR L (l := (SKM.ob D (ΛP - ΛR) (upWord s)).word) pS upS).hom βS).total wS
            (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀ βS).total wS
              (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s))))) := by
  rw [tensorWordQuotientObservation_apply,tensorMatrixCoefficient_observation,
    tensorOriginalWordEntry_vacuum]
  rfl

/-- The source chart sends the source unit to the source-word unit. -/
private theorem source_unit_raw :
    (((tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s).hom βS).total wS
      (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀ βS).total wS
        (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s))) =
      tensorSourceWordUnit D Sc cutoff ΛP ΛR L s :=
  tensorOriginalSourceUnit_wordValue D Sc m cutoff ΛP ΛR L hP hR s

/-- The source path-value chart is its unfolded composite. -/
private theorem source_chart_unfold :
    tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s = (tensorPathValueChart D Sc m cutoff ΛP ΛR L pS upS ≪≫
      eqToIso (congrArg (PowerWordWeight.wordFamily D Tw cutoff L ΛR (ReservoirWord.weight D ΛR cS))
        (congrArg List.reverse (tensorSourceLabels_colors D ΛP ΛR s)))) := by
  unfold tensorSourcePathValueChart
  rfl

/-- The raw value with the word unit unfolded. -/
private theorem source_unit_raw_value :
    (((tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s).hom βS).total wS
      (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀ βS).total wS
        (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s))) =
      PowerWordYoneda.unitVector D Tw cutoff L s.reverse :=
  (source_unit_raw D Sc cutoff L m ΛP ΛR hP hR s).trans
    (tensorSourceWordUnit_formula D Sc cutoff ΛP ΛR L s)

omit [Fintype I] in
/-- The weight of the source word block. -/
private theorem sourceBlock_weight :
    blockWeight D ΛR (s.reverse : Multiset I) = ReservoirWord.weight D ΛR cS :=
  (tensorSourceWordBlock D ΛP ΛR s).2

omit [Fintype I] in
/-- The source word block is the reversed source word with its weight. -/
private theorem source_block_literal : βS = (Subtype.mk (s.reverse : Multiset I) (sourceBlock_weight D ΛP ΛR s) : WeightBlocks D ΛR (ReservoirWord.weight D ΛR cS)) := rfl

/-- The coefficient class at the source block, from the literal block. -/
private theorem coefficient_vacuum_class_of_literal (a : SYM D k) (H :
    tensorTargetWordQuotientEquiv D Sc cutoff L s (tensorSourceLabels_colors D ΛP ΛR s)
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s ((tensorSourceLabels D ΛP ΛR s).map (fun d => d.l.2))
        ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
          ((tensorSourceLabels D ΛP ΛR s).map (fun d => d.l.2)).reverse a (Subtype.mk (s.reverse : Multiset I) (sourceBlock_weight D ΛP ΛR s) : WeightBlocks D ΛR (ReservoirWord.weight D ΛR cS))).total wS
          ((((tensorPathValueChart D Sc m cutoff ΛP ΛR L pS upS)).hom (Subtype.mk (s.reverse : Multiset I) (sourceBlock_weight D ΛP ΛR s) : WeightBlocks D ΛR (ReservoirWord.weight D ΛR cS))).total wS
            (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀ (Subtype.mk (s.reverse : Multiset I) (sourceBlock_weight D ΛP ΛR s) : WeightBlocks D ΛR (ReservoirWord.weight D ΛR cS))).total wS
        (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s))))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) ) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s (tensorSourceLabels_colors D ΛP ΛR s)
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s ((SKM.ob D (ΛP - ΛR) (upWord s)).word.map (fun d => d.l.2))
        ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
          ((SKM.ob D (ΛP - ΛR) (upWord s)).word.map (fun d => d.l.2)).reverse a βS).total wS
          (((tensorPathValueChart D Sc m cutoff ΛP ΛR L (l := (SKM.ob D (ΛP - ΛR) (upWord s)).word) pS upS).hom βS).total wS
            (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀ βS).total wS
              (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s))))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) := H

/-- The coefficient class at the literal source block. -/
private theorem coefficient_vacuum_class_literal (a : SYM D k) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s (tensorSourceLabels_colors D ΛP ΛR s)
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s ((tensorSourceLabels D ΛP ΛR s).map (fun d => d.l.2))
        ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
          ((tensorSourceLabels D ΛP ΛR s).map (fun d => d.l.2)).reverse a (Subtype.mk (s.reverse : Multiset I) (sourceBlock_weight D ΛP ΛR s) : WeightBlocks D ΛR (ReservoirWord.weight D ΛR cS))).total wS
          ((((tensorPathValueChart D Sc m cutoff ΛP ΛR L pS upS)).hom (Subtype.mk (s.reverse : Multiset I) (sourceBlock_weight D ΛP ΛR s) : WeightBlocks D ΛR (ReservoirWord.weight D ΛR cS))).total wS
            (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀ (Subtype.mk (s.reverse : Multiset I) (sourceBlock_weight D ΛP ΛR s) : WeightBlocks D ΛR (ReservoirWord.weight D ΛR cS))).total wS
        (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s))))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) :=
  coefficient_coordinate_unit_class_of_block D Sc cutoff L s _ (tensorSourceLabels_colors D ΛP ΛR s)
    ΛR (ReservoirWord.weight D ΛR cS) (sourceBlock_weight D ΛP ΛR s) _
    (tensorPathValueChart D Sc m cutoff ΛP ΛR L pS upS)
    (tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s)
    (source_chart_unfold D Sc cutoff L m ΛP ΛR s)
    (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀ (Subtype.mk (s.reverse : Multiset I) (sourceBlock_weight D ΛP ΛR s) : WeightBlocks D ΛR (ReservoirWord.weight D ΛR cS))).total wS
        (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s)) a βS (source_block_literal D ΛP ΛR s) wS HEq.rfl
    (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀ βS).total wS
        (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s)) HEq.rfl
    (PowerWordYoneda.unitVector D Tw cutoff L s.reverse) HEq.rfl
    (source_unit_raw_value D Sc cutoff L m ΛP ΛR hP hR s)

/-- The literal row chart sends the source unit to the coefficient class. -/
private theorem coefficient_vacuum_class (a : SYM D k) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s (tensorSourceLabels_colors D ΛP ΛR s)
      (PowerWordQuotientCoordinates.coordinate D Sc cutoff L s ((SKM.ob D (ΛP - ΛR) (upWord s)).word.map (fun d => d.l.2))
        ((tensorWordCoefficientArrow D Sc cutoff ΛR L (ReservoirWord.weight D ΛR cS)
          ((SKM.ob D (ΛP - ΛR) (upWord s)).word.map (fun d => d.l.2)).reverse a βS).total wS
          (((tensorPathValueChart D Sc m cutoff ΛP ΛR L (l := (SKM.ob D (ΛP - ΛR) (upWord s)).word) pS upS).hom βS).total wS
            (((tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom.total R₀ βS).total wS
              (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s))))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) :=
  coefficient_vacuum_class_of_literal D Sc cutoff L m ΛP ΛR hP hR s a
    (coefficient_vacuum_class_literal D Sc cutoff L m ΛP ΛR hP hR s a)

/-- The unchanged canonical observation of the full raw coefficient action
on the actual matrix vacuum is the prescribed source class of coefficient
times identity. This does not identify presentation bubbles with that action. -/
theorem tensorWordQuotientObservation_coefficient_vacuum (a : SYM D k) :
    tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s s pS
      (tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L s
        (SKM.ob D (ΛP - ΛR) (upWord s)) a (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s)) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc a (𝟙 _)) :=
  (coefficient_vacuum_unfold D Sc cutoff L m ΛP ΛR hP hR s a).trans
    (coefficient_vacuum_class D Sc cutoff L m ΛP ΛR hP hR s a)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
