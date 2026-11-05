/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCoefficientAction
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumColumnMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorCoefficientNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerQuotient
import OddMath.QuiverHecke.CyclotomicAction.ELVContentHomVacuum
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumBend

/-! # The decoded coefficient action on the vacuum sector

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8
(the bubble relations of Definition 8.1 at the vacuum sector).

The chosen tensor target family carries the source SYM coefficient action at its
vacuum sector (`tensorTargetFamilyCoefficientAction`). Evaluated at the regular probe
and the empty output block, transported to the tensor vacuum value along a comparison
`c : E Z ≅ V` given by an object equality, and read in the decode chart, the
coefficient of `a` is left multiplication by the class of `a` in the coefficient power
quotient (`vacuumDecode_tensorTargetCoefficient`). This is the coefficient hypothesis
used to read vacuum entries from their decoded values. The computation goes through
the source coefficient on tensor vectors (`sourceCoefficientAction_tensorVector`) and
the weighted empty coordinate (`weightedEmptyEquiv_coefficient_action`). See
`docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory

namespace OddMath.QuiverHecke.ELVOld.VacuumTensorCoefficientMaps
open CyclotomicAction PowerVacuumCoefficient WeightTensorVacuum
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X)
  (L : I × ℕ → ℕ)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "W" => ReservoirWordValue.initialValue D ΛR Sc cutoff L
local notation "vac" => ContentHomSupport.reservoirVacuumBlock D ΛR
local notation "Hv" => VacuumTensor.probeFunctor D Sc m cutoff N
  ((BalancedInduction.restriction (contentInclusion D Sc cutoff N (0 : Multiset I))).obj
    (weightedVacuum D Sc cutoff L))
local notation "V" => Superfunctor.obj Hv (probeOldVacuumRegular D Sc m)
local notation "star" => (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff N 0)
local notation "dec" => tensorVacuumDecodeLinear D Sc m cutoff L
local notation "e" => regularBlock_eq D Sc m cutoff N ΛP ΛR W vac

/-- On the reservoir vacuum block at the vacuum point, the block coefficient action is the
weighted empty-word coefficient arrow. -/
theorem vacuumBlockAction_vacuum_total (q : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (x : (W vac).obj star) :
    ((vacuumBlockAction D Sc cutoff L ΛR vac q).total star) x =
      (weightedVacuum D Sc cutoff L).map (weightedCoefficientEnd D Sc cutoff L q) x := by
  rw [TensorCoefficientNaturality.vacuumBlockAction_total]
  rfl

/-- Conjugated into the tensor vacuum value through the regular-probe evaluation
equality, the source coefficient of `a` decodes to left multiplication by the class
of `a` in the coefficient power quotient. -/
theorem selectedVacuum_coefficient_decode
    (hB : ((selectedHom D Sc m cutoff ΛP ΛR L).obj (regularProbe D Sc m ΛP)) vac = V)
    (a : SKM.SYM D k) (z : (V).obj star) :
    dec ((eqToHom hB.symm ≫ ((sourceCoefficientAction D Sc m cutoff L ΛP ΛR a).total
      (regularProbe D Sc m ΛP)) vac ≫ eqToHom hB).total star z) =
      coefficientPowerQuotientMap D cutoff L a * dec z := by
  obtain ⟨b, rfl⟩ : ∃ b, z = tensorVacuumInputLinear D Sc m cutoff L b :=
    ⟨dec z, (tensorVacuumInput_decode D Sc m cutoff L z).symm⟩
  rw [tensorVacuumDecode_input]
  have h1 : (eqToHom hB.symm).total star (tensorVacuumInputLinear D Sc m cutoff L b) =
      tensorVector D Sc m cutoff N ΛP ΛR W vac star (weightedEmptyEquiv D Sc cutoff L b) := rfl
  have h2 := sourceCoefficientAction_tensorVector D Sc m cutoff L ΛP ΛR a vac star
    (weightedEmptyEquiv D Sc cutoff L b)
  rw [vacuumBlockAction_vacuum_total, weightedEmptyEquiv_coefficient_action] at h2
  rw [Superfunctor.comp_total, Superfunctor.comp_total, SVec.comp_apply, SVec.comp_apply, h1]
  have h3 : ∀ y, dec ((eqToHom hB).total star y) = (weightedEmptyEquiv D Sc cutoff L).symm
      (((selectedIso D Sc m cutoff ΛP ΛR L).hom vac).total star y) := by
    intro y
    have ha : (selectedIso D Sc m cutoff ΛP ΛR L).hom vac =
        eqToHom e ≫ (VacuumTensor.probeVacuumIso D Sc m cutoff N (W vac)).hom := rfl
    rw [ha, Superfunctor.comp_total]
    exact tensorVacuumDecodeLinear_apply D Sc m cutoff L _
  refine (h3 _).trans ?_
  refine (congrArg (weightedEmptyEquiv D Sc cutoff L).symm h2).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The same in the decode chart of endomorphisms: the conjugated source coefficient of `a`
is left multiplication by the class of `a`. -/
theorem selectedVacuum_coefficient_endDecode
    (hB : ((selectedHom D Sc m cutoff ΛP ΛR L).obj (regularProbe D Sc m ΛP)) vac = V)
    (a : SKM.SYM D k) :
    tensorVacuumEndDecode D Sc m cutoff L (eqToHom hB.symm ≫
      ((sourceCoefficientAction D Sc m cutoff L ΛP ΛR a).total (regularProbe D Sc m ΛP)) vac ≫
        eqToHom hB) =
      LinearMap.mulLeft k (coefficientPowerQuotientMap D cutoff L a) := by
  refine tensorVacuumEndDecode_eq_of D Sc m cutoff L _ _ fun z => ?_
  have hz := selectedVacuum_coefficient_decode D Sc m cutoff ΛP ΛR L hB a z
  refine Eq.trans ?_ (hz.trans ?_)
  · congr 1
  · rfl

end OddMath.QuiverHecke.ELVOld.VacuumTensorCoefficientMaps

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
  (cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "S" => selectedHom D Sc m cutoff ΛP ΛR L

/-- Endomorphisms of a Hom input agreeing with the selected one up to the presentation
of its input weight have the same component at the regular probe and the vacuum block. -/
theorem total_heq_of_heq {x : X} (hx : -ΛP = x)
    (F : probeOldWeightSpace D Sc m ΛP x ⟶
      elvWeightSpace D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR
        (ReservoirWord.weight D ΛR 0))
    (hF : HEq F S) (M : ProbeOldWeightProduct D Sc m ΛP x)
    (hM : HEq M (regularProbe D Sc m ΛP))
    (δ : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) (hδ : δ.1 = 0)
    {φ : F ⟶ F} {ψ : S ⟶ S} (h : HEq φ ψ) :
    HEq ((φ.total M) δ) ((ψ.total (regularProbe D Sc m ΛP))
      (ContentHomSupport.reservoirVacuumBlock D ΛR)) := by
  subst hx
  cases hF
  cases hM
  cases h
  have e : δ = ContentHomSupport.reservoirVacuumBlock D ΛR := Subtype.ext hδ
  subst e
  rfl

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ELVOld.WeightTensorVacuum ELVOld.VacuumTensorCoefficientMaps
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X)
  (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "E" => vacuumSectorEvaluation D Sc m cutoff N ΛP ΛR hP hR
local notation "Hv" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff N
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff N (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj Hv (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "Z" => (tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0)).obj
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff N 0)
local notation "dec" => tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L

omit [CommRing k] [Fintype I] in
private theorem eqToEquivalence_inverse_obj_heq' {J : Type*} (C : J → Type*)
    [∀ j, Category (C j)] {a b : J} (e : a = b) (M : C b) :
    HEq ((Pi.eqToEquivalence C e).inverse.obj M) M := by
  subst e
  rfl

omit [AddCommGroup X] [CommRing k] [Fintype I] in
private theorem rec_heq' (T : X → Sort*) {a b : X} (e : a = b) (F : T a) :
    HEq (e ▸ F : T b) F := by
  subst e
  rfl

private theorem map_heq_of_eq {C C' : Type*} [Category C] [Category C'] {F G : C ⥤ C'}
    (h : F = G) {A B : C} (f : A ⟶ B) : HEq (F.map f) (G.map f) := by
  subst h
  rfl

private theorem conj_eq_of_heq {C : Type*} [Category C] {A B T : C} (hA : A = T) (hB : B = T)
    {f : A ⟶ A} {g : B ⟶ B} (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hA = eqToHom hB.symm ≫ g ≫ eqToHom hB := by
  subst hA
  subst hB
  cases h
  rfl

/-- The vacuum-sector evaluation of the target-family coefficient is the source coefficient
at the regular probe and the vacuum block. -/
theorem vacuumSectorEvaluation_coefficient_heq (a : SKM.SYM D k) :
    HEq ((E).map (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom)
      (((sourceCoefficientAction D Tw m cutoff L ΛP ΛR a).total
        (regularProbe D Tw m ΛP)) (ContentHomSupport.reservoirVacuumBlock D ΛR)) := by
  refine (map_heq_of_eq (vacuumSectorEvaluation_eq D Sc m cutoff N ΛP ΛR hP hR) _).trans ?_
  have hZ : HEq Z (selectedHom D Tw m cutoff ΛP ΛR L) := by
    rw [tensorTargetFamily_zero, tensorVacuum_obj, tensorHomAt]
    exact rec_heq' (fun x => probeOldWeightSpace D Tw m ΛP x ⟶
      elvWeightSpace D Tw cutoff N ΛR (ReservoirWord.weight D ΛR 0))
      (probeWeight_vacuum D ΛP).symm _
  have hM : HEq (sectorRegular D Sc m cutoff N ΛP ΛR hP hR) (regularProbe D Tw m ΛP) := by
    unfold sectorRegular
    exact eqToEquivalence_inverse_obj_heq' _ _ _
  exact total_heq_of_heq D Tw m cutoff ΛP ΛR L (probeWeight_vacuum D ΛP).symm Z hZ _ hM _ rfl
    (tensorTargetFamilyCoefficientAction_zero_heq D Sc m cutoff L ΛP ΛR a)

/-- **The decoded vacuum coefficient.** Transported to the tensor vacuum value along an
object equality and read in the decode chart, the target-family coefficient of `a` at the
vacuum sector is left multiplication by the class of `a`. -/
theorem tensorTargetCoefficient_decode (h : (E).obj Z = V) (a : SKM.SYM D k) :
    tensorVacuumEndDecode D Tw m cutoff L (eqToHom h.symm ≫
      (E).map (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom ≫
        eqToHom h) =
      LinearMap.mulLeft k (coefficientPowerQuotientMap D cutoff L a) := by
  have hB : ((selectedHom D Tw m cutoff ΛP ΛR L).obj (regularProbe D Tw m ΛP))
      (ContentHomSupport.reservoirVacuumBlock D ΛR) = V :=
    regularBlock_eq D Tw m cutoff N ΛP ΛR
      (ReservoirWordValue.initialValue D ΛR Tw cutoff L) (ContentHomSupport.reservoirVacuumBlock D ΛR)
  have key := conj_eq_of_heq h hB
    (vacuumSectorEvaluation_coefficient_heq D Sc m cutoff ΛP ΛR L hP hR a)
  refine (congrArg (tensorVacuumEndDecode D Tw m cutoff L) key).trans ?_
  exact selectedVacuum_coefficient_endDecode D Tw m cutoff ΛP ΛR L hB a

/-- The same for any comparison `c : E Z ≅ V` whose forward map is an `eqToHom`; this is
the form of the coefficient hypothesis of `vacuumEntry_of_decode`. -/
theorem vacuumDecode_tensorTargetCoefficient (c : (E).obj Z ≅ V)
    (hc : ∃ h : (E).obj Z = V, c.hom = eqToHom h) (a : SKM.SYM D k) :
    tensorVacuumEndDecode D Tw m cutoff L (c.inv ≫
      (E).map (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom ≫
        c.hom) =
      LinearMap.mulLeft k (coefficientPowerQuotientMap D cutoff L a) := by
  obtain ⟨h, hch⟩ := hc
  have hc' : c = eqToIso h := Iso.ext hch
  subst hc'
  exact tensorTargetCoefficient_decode D Sc m cutoff ΛP ΛR L hP hR h a

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
