import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightModules
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirWordValue

/-! # Tensor vacuum on the original weight products

SwappedVacuumCoordinates §2: the empty formal probe block defines a Hom
input between the full original-weight products. Evaluation at its regular
probe recovers the selected regular-power empty-word family by an even
module isomorphism on every reservoir block and every vector. Contents
with the same original weight are retained, rather than identified.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)

private def forgetEmptyFunctor (ν : List I) (h : ν = []) :
    ProbeEvaluatedModules D Sc m ν ⥤
      Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k) := by
  subst ν
  exact ObjectProperty.ι _

/-- The selected empty-word forgetting map, exposed for the native vacuum cap chart. -/
abbrev emptyContentForget (ν : List I) (h : ν = []) :
    ProbeEvaluatedModules D Sc m ν ⥤
      Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k) :=
  forgetEmptyFunctor D Sc m ν h

private instance (ν : List I) (h : ν = []) :
    (forgetEmptyFunctor D Sc m ν h).Additive := by
  subst ν
  exact ⟨by intros; rfl⟩

private instance (ν : List I) (h : ν = []) :
    (forgetEmptyFunctor D Sc m ν h).Linear k := by
  subst ν
  exact ⟨fun _ _ => rfl⟩

private instance (ν : List I) (h : ν = []) :
    IsSuperfunctor k (forgetEmptyFunctor D Sc m ν h) := by
  subst ν
  exact ⟨fun hf => hf⟩

private def regularEmpty (ν : List I) (h : ν = []) :
    ProbeEvaluatedModules D Sc m ν := by
  subst ν
  exact ⟨probeOldVacuumRegular D Sc m, probeOldVacuumRegular_evaluates D Sc m⟩

private theorem forget_regular (ν : List I) (h : ν = []) :
    (forgetEmptyFunctor D Sc m ν h).obj (regularEmpty D Sc m ν h) =
      probeOldVacuumRegular D Sc m := by
  subst ν
  rfl

/-- The empty formal content at the lowest original probe weight. -/
def emptyBlock (Λ : X) : WeightBlocks D Λ (-Λ) := ⟨0, blockWeight_zero D Λ⟩

/-- Evaluate only at formal content zero, retaining the other source blocks. -/
def emptyProbe (Λ : X) :
    Superfunctor k (ProbeOldWeightProduct D Sc m Λ (-Λ))
      (Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k)) :=
  (probeOldBlockEval D Sc m Λ (emptyBlock D Λ)).comp
    ⟨forgetEmptyFunctor D Sc m (0 : Multiset I).toList Multiset.toList_zero⟩

private def regularAt (β : Multiset I) (h : β = 0) : ProbeCanonicalModules D Sc m β := by
  subst β
  exact regularEmpty D Sc m _ Multiset.toList_zero

/-- The evaluated regular probe at formal content zero, with zero modules
at every other content, including collisions in the original weight group. -/
def regularProbe (Λ : X) : ProbeOldWeightProduct D Sc m Λ (-Λ) :=
  fun β => if h : β.1 = 0 then regularAt D Sc m β.1 h
    else probeOldZeroModule D Sc m β.1

theorem emptyProbe_regular (Λ : X) :
    (emptyProbe D Sc m Λ).obj (regularProbe D Sc m Λ) = probeOldVacuumRegular D Sc m := by
  change (forgetEmptyFunctor D Sc m _ Multiset.toList_zero).obj
    (if h : (0 : Multiset I) = 0 then regularAt D Sc m 0 h
      else probeOldZeroModule D Sc m 0) = _
  rw [dite_eq_left rfl]
  exact forget_regular D Sc m _ Multiset.toList_zero

private theorem probeScalar_mem :
    SVec.ofHom (probeVacuumScalarEquiv D Sc m).symm.toLinearMap ∈
      parity (R := k) ((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m))
        SVec.unit 0 := by
  intro q
  apply LinearMap.ext
  intro v
  change (probeVacuumScalarEquiv D Sc m).symm
      (((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)).proj q v) =
    (SVec.unit (k := k)).proj (q + 0) ((probeVacuumScalarEquiv D Sc m).symm v)
  rw [SVec.proj_apply_of_mem_part _ (p := q) (probeVacuum_even D Sc m v)]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simp only [ite_true, add_zero]
    exact (SVec.unit_proj_zero_apply _).symm
  · simp only [one_ne_zero, ite_false, map_zero, add_zero]
    exact (SVec.unit_proj_one_apply _).symm

variable (cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (W : ELVWeightProduct D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0))

/-- Tensor with the reservoir family after empty formal probe evaluation. -/
def blockFunctor (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    Superfunctor k (ProbeOldWeightProduct D Sc m ΛP (-ΛP))
      (ContentModules D Sc cutoff bound β.1) :=
  (emptyProbe D Sc m ΛP).comp
    (VacuumTensor.superfunctor (W β) (probeOldVacuumObject D Sc m))

def functor : ProbeOldWeightProduct D Sc m ΛP (-ΛP) ⥤
    ELVWeightProduct D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0) :=
  Functor.pi' fun β => (blockFunctor D Sc m cutoff bound ΛP ΛR W β).toFunctor

instance : (functor D Sc m cutoff bound ΛP ΛR W).Additive where
  map_add := funext fun β => (blockFunctor D Sc m cutoff bound ΛP ΛR W β).toFunctor.map_add

instance : (functor D Sc m cutoff bound ΛP ΛR W).Linear k where
  map_smul f r := funext fun β =>
    (blockFunctor D Sc m cutoff bound ΛP ΛR W β).toFunctor.map_smul r f

instance : IsSuperfunctor k (functor D Sc m cutoff bound ΛP ΛR W) where
  map_mem hf β := IsSuperfunctor.map_mem
    (F := (blockFunctor D Sc m cutoff bound ΛP ΛR W β).toFunctor) hf

/-- A swapped Hom input between the two full original-weight products. -/
def hom : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
    elvWeightSpace D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0) :=
  ⟨functor D Sc m cutoff bound ΛP ΛR W⟩

/-- The prescribed regular-probe evaluation before applying the scalar chart. -/
theorem regularBlock_eq (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    ((hom D Sc m cutoff bound ΛP ΛR W).obj (regularProbe D Sc m ΛP)) β =
      VacuumTensor.object (W β)
        ((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)) :=
  congrArg (fun M => (VacuumTensor.superfunctor (W β)
    (probeOldVacuumObject D Sc m)).obj M) (emptyProbe_regular D Sc m ΛP)

private def blockIso (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    ((hom D Sc m cutoff bound ΛP ΛR W).obj (regularProbe D Sc m ΛP)) β ≅ W β :=
  eqToIso (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β) ≪≫
    VacuumTensor.scalarTensorIso (W β) _ (probeVacuumScalarEquiv D Sc m).symm
      (probeScalar_mem D Sc m)

/-- The tensor-vacuum Hom input evaluated at its specified regular probe
recovers the entire reservoir family, with no assumed comparison. -/
def regularIso :
    (hom D Sc m cutoff bound ΛP ΛR W).obj (regularProbe D Sc m ΛP) ≅ W :=
  Pi.isoMk (blockIso D Sc m cutoff bound ΛP ΛR W)

theorem regularIso_hom_mem :
    (regularIso D Sc m cutoff bound ΛP ΛR W).hom ∈ parity (R := k) _ _ 0 := by
  intro β
  exact comp_mem (eqToHom_mem_parity_zero (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β))
    (VacuumTensor.scalarTensorIso_hom_mem _ _ _ _)

/-- The regular tensor vector carrying an arbitrary reservoir coefficient. -/
def tensorVector (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (c : ContentCategory D Sc cutoff bound β.1) (v : (W β).obj c) :
    (((hom D Sc m cutoff bound ΛP ΛR W).obj (regularProbe D Sc m ΛP)) β).obj c :=
  (eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β).symm).total c
    (v ⊗ₜ[k] probeVacuumScalarEquiv D Sc m 1)

theorem regularIso_hom_tensorVector
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (c : ContentCategory D Sc cutoff bound β.1) (v : (W β).obj c) :
    ((regularIso D Sc m cutoff bound ΛP ΛR W).hom β).total c
      (tensorVector D Sc m cutoff bound ΛP ΛR W β c v) = v := by
  let f := (VacuumTensor.scalarTensorIso (W β) _
    (probeVacuumScalarEquiv D Sc m).symm (probeScalar_mem D Sc m)).hom
  have h : eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β).symm ≫
      (regularIso D Sc m cutoff bound ΛP ΛR W).hom β = f := by
    change eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β).symm ≫
      (eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β) ≫ f) = f
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have ht := congrArg (fun g => g.total c) h
  rw [Superfunctor.comp_total] at ht
  change ((eqToHom (regularBlock_eq D Sc m cutoff bound ΛP ΛR W β).symm).total c ≫
    ((regularIso D Sc m cutoff bound ΛP ΛR W).hom β).total c)
      (v ⊗ₜ[k] probeVacuumScalarEquiv D Sc m 1) = v
  rw [ht]
  exact (VacuumTensor.scalarTensorIso_hom_tmul (W β) _
    (probeVacuumScalarEquiv D Sc m).symm (probeScalar_mem D Sc m) c v
      (probeVacuumScalarEquiv D Sc m 1)).trans (by
        rw [LinearEquiv.symm_apply_apply, one_smul])

variable (L : I × ℕ → ℕ)

/-- The selected regular-power tensor-vacuum Hom input at sector `(0,0)`. -/
def selectedHom : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
    elvWeightSpace D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR
      (ReservoirWord.weight D ΛR 0) :=
  hom D Sc m cutoff _ ΛP ΛR (ReservoirWordValue.initialValue D ΛR Sc cutoff L)

/-- Its reservoir value at the actual regular probe is the already selected
regular-power empty-word family on every original-weight block. -/
def selectedIso :
    (selectedHom D Sc m cutoff ΛP ΛR L).obj (regularProbe D Sc m ΛP) ≅
      ReservoirWordValue.initialValue D ΛR Sc cutoff L :=
  regularIso D Sc m cutoff _ ΛP ΛR _

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
