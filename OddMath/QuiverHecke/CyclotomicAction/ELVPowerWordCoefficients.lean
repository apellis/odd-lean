import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeightContexts
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientModuleMaps

/-! # Coefficient insertion in signed word coordinates

SwappedVacuumCoordinates §§4–6: identify the genuine coefficient module
maps with the signed old-Hom operators before transporting chosen E values.
The full coefficient algebra and chronological multiplication are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordCoefficients
open CyclotomicAction CyclotomicCrossingTensor
universe u
section Generic
variable {C : Type*} [Category* C]
private def conjugate {A B : C} (e : A ≅ B) (f : End B) : End A := e.hom ≫ f ≫ e.inv
private theorem conjugate_cancel {A B : C} (e : A ≅ B) (f : End B) :
    conjugate e f ≫ e.hom = e.hom ≫ f := by
  simp only [conjugate, Category.assoc, Iso.inv_hom_id, Category.comp_id]
private theorem conjugate_comp {A B : C} (e : A ≅ B) (f g : End B) :
    conjugate e (f ≫ g) = conjugate e f ≫ conjugate e g := by
  simp only [conjugate, Category.assoc, Iso.inv_hom_id_assoc]
private theorem conjugate_neg [Preadditive C] {A B : C} (e : A ≅ B) (f : End B) :
    conjugate e (-f) = -conjugate e f := by
  change e.hom ≫ ((-f) ≫ e.inv) = -(e.hom ≫ (f ≫ e.inv))
  exact (congrArg (fun h => e.hom ≫ h) (Preadditive.neg_comp f e.inv)).trans
    (Preadditive.comp_neg e.hom (f ≫ e.inv))
private theorem conjugate_square {A B E : C} (e : A ≅ B) (f : B ≅ E)
    (x : End B) (y : End E) (h : x ≫ f.hom = f.hom ≫ y) :
    conjugate e x ≫ (e ≪≫ f).hom = (e ≪≫ f).hom ≫ y := by
  simp only [conjugate, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]
end Generic
private theorem mapped_square {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {A P : C} {E : B} (e : A ≅ P) (f : F.obj P ≅ E)
    (x : End A) (y : End P) (z : End E)
    (hx : x ≫ e.hom = e.hom ≫ y) (hf : F.map y ≫ f.hom = f.hom ≫ z) :
    F.map x ≫ (F.mapIso e ≪≫ f).hom = (F.mapIso e ≪≫ f).hom ≫ z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← F.map_comp, hx, F.map_comp, Category.assoc, hf]

private theorem map_end_neg {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Preadditive B] (F : C ⥤ B) [F.Additive] (A : C) (f : End A) :
    F.map (-f) = -F.map f := Functor.map_neg F

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The genuine full coefficient module action is the signed old-Hom
operator at every word, including inhomogeneous coefficients. -/
theorem coefficient_fromArrow (ν : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a =
      PowerWordMorphisms.fromArrow D Sc cutoff L ν ν (coefficientEndomorphism D Sc cutoff ν a) := by
  apply (PowerWordYoneda.homEquiv D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)).injective
  change PowerWordYoneda.evaluate D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)
      (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a) =
    PowerWordYoneda.evaluate D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)
      (PowerWordMorphisms.fromArrow D Sc cutoff L ν ν (coefficientEndomorphism D Sc cutoff ν a))
  rw [show PowerWordYoneda.evaluate D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)
      (PowerWordMorphisms.fromArrow D Sc cutoff L ν ν (coefficientEndomorphism D Sc cutoff ν a)) =
    powerWordGenerator D Sc cutoff L ν (OldCategory.mk ν) (coefficientEndomorphism D Sc cutoff ν a) from
      PowerWordYoneda.evaluate_fromElement D Sc cutoff L ν (powerWordObject D Sc cutoff L ν) _]
  change (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a).total (OldCategory.mk ν)
    (PowerWordYoneda.unitVector D Sc cutoff L ν) = _
  rw [coefficientModuleAction_total]
  change (powerWordModule D Sc cutoff L ν).map (coefficientEndomorphism D Sc cutoff ν a)
    (powerWordGenerator D Sc cutoff L ν (OldCategory.mk ν) (𝟙 _)) = _
  simpa only [Category.id_comp] using PowerWordYoneda.generator_naturality D Sc cutoff L ν
    (coefficientEndomorphism D Sc cutoff ν a) (𝟙 _)

/-- The generator formula retains the full old arrow inside its total parity twist. -/
theorem coefficient_generator (ν : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (p : ZMod 2)
    (w : OldCategory D Sc cutoff) (h : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ w) :
    (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a).app p w
      (powerWordGenerator D Sc cutoff L ν w h) =
    powerWordGenerator D Sc cutoff L ν w (proj k p (coefficientEndomorphism D Sc cutoff ν a) ≫ twist k p h) := by
  rw [coefficient_fromArrow]
  exact PowerWordMorphisms.fromArrow_generator D Sc cutoff L ν ν _ p w h

/-- Even on a tensor with its own coefficient tail, the twist includes both
that coefficient and the affine arrow. No ordinary commutativity is used. -/
theorem coefficient_tensor (ν : List I)
    (a b : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (p : ZMod 2)
    (w : OldCategory D Sc cutoff) (h : (OldCategory.mk ν : OldCategory D Sc cutoff) ⟶ w) :
    (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a).app p w
      (BalancedInduction.tensor (powerWordCoefficientSource D Sc cutoff ν)
        (liftedPowerRegular D cutoff L).toFunctor (powerCoefficientStar D cutoff) h
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k b)) =
    powerWordGenerator D Sc cutoff L ν w
      (proj k p (coefficientEndomorphism D Sc cutoff ν a) ≫
        twist k p (coefficientEndomorphism D Sc cutoff ν b ≫ h)) := by
  rw [coefficient_fromArrow]
  exact PowerWordMorphisms.fromArrow_tensor D Sc cutoff L ν ν _ p w h b

/-- Right extension preserves the literal coefficient endomorphism. -/
theorem extended_coefficient (ν η : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    PowerWordContexts.extendedArrow D Sc cutoff ν ν η (coefficientEndomorphism D Sc cutoff ν a) =
      coefficientEndomorphism D Sc cutoff (PowerWordContexts.extendedWord ν η) a := by
  induction η generalizing ν with
  | nil => rfl
  | cons i η ih =>
      change PowerWordContexts.extendedArrow D Sc cutoff (ν ++ [i]) (ν ++ [i]) η
        ((append D Sc cutoff i).map (coefficientEndomorphism D Sc cutoff ν a)) = _
      rw [append_coefficientEndomorphism, ih]
      rfl

private theorem weightedHom_neg (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (f : End M) :
    weightedModuleHom D Sc cutoff N M M hM hM (-f) =
      -weightedModuleHom D Sc cutoff N M M hM hM f := rfl

private def vacuumMap (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    End (powerWordModule D Sc cutoff L []) := vacuumCoefficientAction D Sc cutoff L a

private theorem vacuumMap_mk (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    vacuumMap D Sc cutoff L
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) =
    coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L []) a :=
  powerModuleCoefficientAction_mk D Sc cutoff L (coefficientPowerVacuumObject D Sc cutoff L) a

section Weight
variable [Fintype I] (Λ : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
/-- The genuine regular A/T vacuum coefficient map, descended and restricted
to every block of the same weight family. -/
def vacuumFamilyCoefficient (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    End (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ []) []) :=
  fun β => (BalancedInduction.restriction (contentInclusion D Sc cutoff N β.1)).map
    (weightedModuleHom D Sc cutoff N (powerWordModule D Sc cutoff L []) (powerWordModule D Sc cutoff L [])
      (PowerWordContent.word_killsWeighted D Sc cutoff L []) (PowerWordContent.word_killsWeighted D Sc cutoff L [])
      (vacuumMap D Sc cutoff L a))

/-- The vacuum coefficient insertion is the literal full signed old-Hom map. -/
theorem vacuumFamilyCoefficient_mk (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    vacuumFamilyCoefficient D Sc cutoff L Λ
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) =
    PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ []) [] []
      (coefficientEndomorphism D Sc cutoff [] a) := by
  funext β
  unfold vacuumFamilyCoefficient
  rw [vacuumMap_mk, coefficient_fromArrow]
  rfl

private theorem vacuumFamilyCoefficient_mul (a b : CoefficientPowerQuotient (k := k) D cutoff L) :
    vacuumFamilyCoefficient D Sc cutoff L Λ (a * b) =
      vacuumFamilyCoefficient D Sc cutoff L Λ b ≫ vacuumFamilyCoefficient D Sc cutoff L Λ a := by
  have hm : vacuumMap D Sc cutoff L (a * b) = vacuumMap D Sc cutoff L b ≫ vacuumMap D Sc cutoff L a :=
    (vacuumCoefficientAction D Sc cutoff L).map_mul a b
  funext β
  change (BalancedInduction.restriction (contentInclusion D Sc cutoff N β.1)).map
    (weightedModuleHom D Sc cutoff N (powerWordModule D Sc cutoff L []) (powerWordModule D Sc cutoff L [])
      (PowerWordContent.word_killsWeighted D Sc cutoff L []) (PowerWordContent.word_killsWeighted D Sc cutoff L [])
      (vacuumMap D Sc cutoff L (a * b))) = _
  rw [hm, weightedModuleHom_comp, Functor.map_comp]
  rfl

private theorem vacuumFamilyCoefficient_neg (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    vacuumFamilyCoefficient D Sc cutoff L Λ (-a) = -vacuumFamilyCoefficient D Sc cutoff L Λ a := by
  have hm : vacuumMap D Sc cutoff L (-a) = -vacuumMap D Sc cutoff L a :=
    (vacuumCoefficientAction D Sc cutoff L).map_neg a
  funext β
  change (BalancedInduction.restriction (contentInclusion D Sc cutoff N β.1)).map
    (weightedModuleHom D Sc cutoff N (powerWordModule D Sc cutoff L []) (powerWordModule D Sc cutoff L [])
      (PowerWordContent.word_killsWeighted D Sc cutoff L []) (PowerWordContent.word_killsWeighted D Sc cutoff L [])
      (vacuumMap D Sc cutoff L (-a))) = _
  rw [hm, weightedHom_neg, Functor.map_neg]
  rfl

/-- Literal whiskering of the given regular A/T coefficient action by the
chosen E-word functors. No coordinate-defined substitute action is used. -/
def coefficientValue (a : CoefficientPowerQuotient (k := k) D cutoff L) (ν : List I) :
    End (PowerWordEvaluation.value D Sc cutoff L Λ ν) :=
  ν.reverseRecOn
    (conjugate (eqToIso (PowerWordEvaluation.value_nil D Sc cutoff L Λ))
      (vacuumFamilyCoefficient D Sc cutoff L Λ a))
    (fun ρ i f => conjugate (eqToIso (PowerWordEvaluation.value_append D Sc cutoff L Λ ρ i))
      ((elvEFunctor D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ρ i)).map f))

theorem coefficientValue_nil (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    coefficientValue D Sc cutoff L Λ a [] =
    conjugate (eqToIso (PowerWordEvaluation.value_nil D Sc cutoff L Λ))
      (vacuumFamilyCoefficient D Sc cutoff L Λ a) := by
  simp only [coefficientValue, List.reverseRecOn_nil]

theorem coefficientValue_append (a : CoefficientPowerQuotient (k := k) D cutoff L) (ν : List I) (i : I) :
    coefficientValue D Sc cutoff L Λ a (ν ++ [i]) =
    conjugate (eqToIso (PowerWordEvaluation.value_append D Sc cutoff L Λ ν i))
      ((elvEFunctor D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).map
        (coefficientValue D Sc cutoff L Λ a ν)) := by
  simp only [coefficientValue, List.reverseRecOn_concat]

/-- The given vacuum insertion in its selected native value chart, for
an arbitrary A/T coefficient rather than only a chosen representative. -/
theorem coefficientValue_vacuum (a : CoefficientPowerQuotient (k := k) D cutoff L) :
    coefficientValue D Sc cutoff L Λ a [] ≫ (PowerWordEvaluation.chart D Sc cutoff L Λ []).hom =
      (PowerWordEvaluation.chart D Sc cutoff L Λ []).hom ≫ vacuumFamilyCoefficient D Sc cutoff L Λ a := by
  rw [coefficientValue_nil, PowerWordEvaluation.chart_nil]
  exact conjugate_cancel _ _

/-- Chronological composition retains the original, possibly noncommuting
coefficient multiplication order after actual E-word whiskering. -/
theorem coefficientValue_mul (a b : CoefficientPowerQuotient (k := k) D cutoff L) (ν : List I) :
    coefficientValue D Sc cutoff L Λ (a * b) ν =
      coefficientValue D Sc cutoff L Λ b ν ≫ coefficientValue D Sc cutoff L Λ a ν := by
  induction ν using List.reverseRecOn with
  | nil => simp only [coefficientValue_nil, vacuumFamilyCoefficient_mul, conjugate_comp]
  | append_singleton ν i ih =>
      simp only [coefficientValue_append, ih, Functor.map_comp, conjugate_comp]

/-- Negation of an arbitrary quotient coefficient is retained by actual
E-word whiskering; this detects the sign between two distinct odd colours. -/
theorem coefficientValue_neg (a : CoefficientPowerQuotient (k := k) D cutoff L) (ν : List I) :
    coefficientValue D Sc cutoff L Λ (-a) ν = -coefficientValue D Sc cutoff L Λ a ν := by
  induction ν using List.reverseRecOn with
  | nil => simp only [coefficientValue_nil, vacuumFamilyCoefficient_neg, conjugate_neg]
  | append_singleton ν i ih =>
      simp only [coefficientValue_append, ih]
      exact (congrArg
        (conjugate (eqToIso (PowerWordEvaluation.value_append D Sc cutoff L Λ ν i)))
        (map_end_neg (elvEFunctor D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i))
          (PowerWordEvaluation.value D Sc cutoff L Λ ν) (coefficientValue D Sc cutoff L Λ a ν))).trans
        (conjugate_neg _ _)

/-- The actual regular A/T coefficient action, whiskered by the given E
functors, has the full signed old-Hom coordinate in the selected word chart. -/
theorem coefficient_value (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (ν : List I) :
    coefficientValue D Sc cutoff L Λ
      ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) ν ≫
        (PowerWordEvaluation.chart D Sc cutoff L Λ ν).hom =
    (PowerWordEvaluation.chart D Sc cutoff L Λ ν).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν ν
        (coefficientEndomorphism D Sc cutoff ν a) := by
  induction ν using List.reverseRecOn with
  | nil =>
      rw [coefficientValue_nil, PowerWordEvaluation.chart_nil, vacuumFamilyCoefficient_mk]
      exact conjugate_cancel _ _
  | append_singleton ν i ih =>
      have ha := PowerWordWeightWhiskering.append_family_arrow D Sc cutoff L Λ ν ν i
        (PowerWordWeight.wordWeight D Λ ν) (PowerWordWeight.wordWeight D Λ (ν ++ [i]))
        rfl rfl rfl rfl (PowerWordWeight.wordWeight_append D Λ ν i) rfl
        (coefficientEndomorphism D Sc cutoff ν a)
      rw [append_coefficientEndomorphism] at ha
      simp only [coefficientValue_append, PowerWordEvaluation.chart_append]
      exact conjugate_square
        (eqToIso (PowerWordEvaluation.value_append D Sc cutoff L Λ ν i))
        ((elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).toFunctor.mapIso
          (PowerWordEvaluation.chart D Sc cutoff L Λ ν) ≪≫ PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i)
        _ _ (mapped_square
          (elvE D Sc cutoff N i Λ (PowerWordWeight.wordWeight_append D Λ ν i)).toFunctor
          (PowerWordEvaluation.chart D Sc cutoff L Λ ν) (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i)
          _ _ _ ih ha)

/-- The genuine coefficient insertion on a literal E-word value, inside
any chosen right E-context, retains the same full coefficient at the
extended word. Every component and coefficient vector is included. -/
theorem coefficient_in_context (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (ν η : List I) :
    (PowerWordWeightContexts.contextFunctor D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) η).map
      (coefficientValue D Sc cutoff L Λ
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a) ν) ≫
      (PowerWordWeightContexts.contextChart D Sc cutoff L Λ ν η _ rfl
        (PowerWordEvaluation.chart D Sc cutoff L Λ ν)).hom =
    (PowerWordWeightContexts.contextChart D Sc cutoff L Λ ν η _ rfl
      (PowerWordEvaluation.chart D Sc cutoff L Λ ν)).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ
        (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D Λ ν) η)
        (PowerWordContexts.extendedWord ν η) (PowerWordContexts.extendedWord ν η)
        (coefficientEndomorphism D Sc cutoff (PowerWordContexts.extendedWord ν η) a) := by
  have hc :
      (PowerWordWeightContexts.contextFunctor D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) η).map
        (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν ν
          (coefficientEndomorphism D Sc cutoff ν a)) ≫
        (PowerWordWeightContexts.contextIso D Sc cutoff L Λ ν (PowerWordWeight.wordWeight D Λ ν) rfl η).hom =
      (PowerWordWeightContexts.contextIso D Sc cutoff L Λ ν (PowerWordWeight.wordWeight D Λ ν) rfl η).hom ≫
        PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L Λ
          (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D Λ ν) η)
          (PowerWordContexts.extendedWord ν η) (PowerWordContexts.extendedWord ν η)
          (PowerWordContexts.extendedArrow D Sc cutoff ν ν η (coefficientEndomorphism D Sc cutoff ν a)) :=
    PowerWordWeightContexts.context_family_arrow D Sc cutoff L Λ ν ν η
      (PowerWordWeight.wordWeight D Λ ν) rfl rfl rfl (coefficientEndomorphism D Sc cutoff ν a)
  rw [extended_coefficient] at hc
  exact mapped_square
    (PowerWordWeightContexts.contextFunctor D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) η)
    (PowerWordEvaluation.chart D Sc cutoff L Λ ν)
    (PowerWordWeightContexts.contextIso D Sc cutoff L Λ ν (PowerWordWeight.wordWeight D Λ ν) rfl η)
    _ _ _ (coefficient_value D Sc cutoff L Λ a ν) hc
end Weight
end OddMath.QuiverHecke.ELVOld.PowerWordCoefficients
