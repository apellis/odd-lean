/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumColumnMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumBend
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorFaithful
import OddMath.QuiverHecke.CyclotomicAction.ELVRegularProbeGenerating

/-! # Faithfulness of the decoded vacuum reading

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8
(the bubble relations of Definition 8.1 at the vacuum sector).

An endomorphism of the selected tensor-vacuum Hom input is a supernatural
transformation of a superfunctor into the product of the reservoir content blocks.
Off the vacuum block its components land in zero objects; on the vacuum block the
superfunctor is the empty probe evaluation followed by the tensor vacuum, and the
regular probe generates the empty block (`regularProbe_generating`), so the
transformation is determined by its total component at the regular probe
(`selectedHom_end_ext`).

Transporting along the weight presentations of the vacuum sector, the reading
`f ↦ tensorVacuumEndDecode (c.inv ≫ E.map f ≫ c.hom)` of endomorphisms of the
vacuum object of the tensor target family, with `E = vacuumSectorEvaluation`, is
injective for every comparison `c : E Z ≅ V`
(`vacuumDecodeFaithful_tensorTarget`). The statement is the faithfulness
hypothesis used to read vacuum entries from their decoded values. See
`docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction SwappedAssembly
universe u

section Block
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
  (cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "S" => selectedHom D Sc m cutoff ΛP ΛR L
local notation "W₀" => ReservoirWordValue.initialValue D ΛR Sc cutoff L

/-- The block component of an endomorphism of the selected Hom input. -/
def selectedBlockEnd (φ : S ⟶ S) (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    blockFunctor D Sc m cutoff N ΛP ΛR W₀ β ⟶ blockFunctor D Sc m cutoff N ΛP ΛR W₀ β where
  app p Y := (φ.app p Y) β
  app_mem p Y := φ.app_mem p Y β
  naturality p {_ _} _ f hf := congrFun (φ.naturality p f hf) β

/-- An endomorphism of the selected tensor-vacuum Hom input is determined by its
total component at the regular probe, on the reservoir vacuum block. -/
theorem selectedHom_end_ext {φ ψ : S ⟶ S}
    (h : (φ.total (regularProbe D Sc m ΛP)) (ContentHomSupport.reservoirVacuumBlock D ΛR) =
      (ψ.total (regularProbe D Sc m ΛP)) (ContentHomSupport.reservoirVacuumBlock D ΛR)) :
    φ = ψ := by
  apply Superfunctor.hom_ext
  intro p Y
  funext β
  by_cases hβ : β = ContentHomSupport.reservoirVacuumBlock D ΛR
  · subst hβ
    have e := VacuumTensor.hom_ext_of_generating_total
      (W₀ (ContentHomSupport.reservoirVacuumBlock D ΛR)) (probeOldVacuumObject D Sc m)
      (emptyProbe D Sc m ΛP) (regularVector D Sc m ΛP)
      (fun X q n hn => regularProbe_generating D Sc m ΛP X q n hn)
      (φ := selectedBlockEnd D Sc m cutoff ΛP ΛR L φ _)
      (ψ := selectedBlockEnd D Sc m cutoff ΛP ΛR L ψ _) h
    exact congrArg (fun χ => SuperNatTrans.app χ p Y) e
  · exact (ContentHomSupport.selectedVacuum_off_isZero D Sc m cutoff ΛP ΛR L Y β hβ).eq_of_tgt
      _ _

/-- The same determination for any Hom input agreeing with the selected one up to
the presentation of its input weight. -/
theorem end_ext_of_heq {x : X} (hx : -ΛP = x)
    (F : probeOldWeightSpace D Sc m ΛP x ⟶
      elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0))
    (hF : HEq F S) (M : ProbeOldWeightProduct D Sc m ΛP x)
    (hM : HEq M (regularProbe D Sc m ΛP))
    (δ : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) (hδ : δ.1 = 0)
    {φ ψ : F ⟶ F} (h : (φ.total M) δ = (ψ.total M) δ) : φ = ψ := by
  subst hx
  cases hF
  cases hM
  have e : δ = ContentHomSupport.reservoirVacuumBlock D ΛR := Subtype.ext hδ
  subst e
  exact selectedHom_end_ext D Sc m cutoff ΛP ΛR L h

end Block

section Decode
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem emptyContent_eq (N : ℕ) (w : ContentCategory D Sc cutoff N 0) :
    w = ⟨⟨[]⟩, rfl⟩ := by
  rcases w with ⟨⟨w⟩, hw⟩
  have he : w = [] := by simpa only [Multiset.coe_eq_zero] using hw
  subst w
  rfl

variable [Fintype I] (m : I → ℕ) (L : I × ℕ → ℕ)

/-- Reading endomorphisms of the tensor vacuum value at the vacuum point in the
decode chart is injective: the content-zero category has the vacuum point as its
only object. -/
theorem tensorVacuumEndDecode_injective :
    Function.Injective (tensorVacuumEndDecode D Sc m cutoff L) := by
  intro f g h
  have h' := ((tensorVacuumDecodeEquiv D Sc m cutoff L).conjAlgEquiv k).injective h
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro w
  rw [emptyContent_eq D Sc cutoff _ w]
  exact h'

end Decode
end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ELVOld.WeightTensorVacuum
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X)
  (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "E" => vacuumSectorEvaluation D Sc m cutoff N ΛP ΛR hP hR
local notation "Hv" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff N
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff N (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj Hv (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "Z" => (tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0)).obj

omit [CommRing k] [Fintype I] in
private theorem eqToEquivalence_inverse_obj_heq {J : Type*} (C : J → Type*)
    [∀ j, Category (C j)] {a b : J} (e : a = b) (M : C b) :
    HEq ((Pi.eqToEquivalence C e).inverse.obj M) M := by
  subst e
  rfl

omit [AddCommGroup X] [CommRing k] [Fintype I] in
private theorem rec_heq (T : X → Sort*) {a b : X} (e : a = b) (F : T a) :
    HEq (e ▸ F : T b) F := by
  subst e
  rfl

/-- The vacuum-sector evaluation of an endomorphism of the vacuum object of the tensor
target family determines the endomorphism. -/
theorem vacuumSectorEvaluation_map_injective :
    Function.Injective (fun f : Z ⟶ Z => (E).map f) := by
  intro f g hfg
  have h2 : (E).map f = (E).map g := hfg
  rw [vacuumSectorEvaluation_eq] at h2
  have hZ : HEq Z (selectedHom D (parameterTwist D Sc) m cutoff ΛP ΛR L) := by
    rw [tensorTargetFamily_zero, tensorVacuum_obj, tensorHomAt]
    exact rec_heq (fun x => probeOldWeightSpace D (parameterTwist D Sc) m ΛP x ⟶
      elvWeightSpace D (parameterTwist D Sc) cutoff N ΛR (ReservoirWord.weight D ΛR 0))
      (probeWeight_vacuum D ΛP).symm _
  have hM : HEq (sectorRegular D Sc m cutoff N ΛP ΛR hP hR)
      (regularProbe D (parameterTwist D Sc) m ΛP) := by
    unfold sectorRegular
    exact eqToEquivalence_inverse_obj_heq _ _ _
  exact end_ext_of_heq D (parameterTwist D Sc) m cutoff ΛP ΛR L
    (probeWeight_vacuum D ΛP).symm Z hZ _ hM _ rfl h2

/-- **Faithfulness of the decoded vacuum reading.** For every comparison
`c : E Z ≅ V`, the reading `f ↦ tensorVacuumEndDecode (c.inv ≫ E.map f ≫ c.hom)` of
endomorphisms of the vacuum object `Z` of the tensor target family is injective. -/
theorem vacuumDecodeFaithful_tensorTarget (c : (E).obj Z ≅ V) :
    Function.Injective (fun f : Z ⟶ Z =>
      tensorVacuumEndDecode D (parameterTwist D Sc) m cutoff L (c.inv ≫ (E).map f ≫ c.hom)) := by
  intro f g hfg
  have h1 := tensorVacuumEndDecode_injective D (parameterTwist D Sc) cutoff m L hfg
  apply vacuumSectorEvaluation_map_injective D Sc m cutoff ΛP ΛR L hP hR
  have h3 := congrArg (fun t => c.hom ≫ t ≫ c.inv) h1
  simpa only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h3

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
