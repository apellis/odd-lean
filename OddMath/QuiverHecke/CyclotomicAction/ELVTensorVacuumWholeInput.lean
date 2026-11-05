import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightPreCap
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumMomentMaps
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorVacuum
import OddMath.SKM.RouquierHomWeightCoordinates

/-! # The whole-output tensor input at the vacuum weights

SwappedVacuumCoordinates §§2–3: the tensor input used by the native
pre-cap retains every output block. Its empty-probe pullback is the
specified supported tensor Hom, with both weight presentations retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction SwappedAssembly
universe u
local instance tensorWholeHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛR : X)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "W" => ReservoirWordValue.initialValue D ΛR Sc cutoff L

private def tensorOutputFunctor : ProbeVacuumCap.modulePiCategory D Sc m ⥤
    ELVWeightProduct D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0) :=
  Functor.pi' fun β => (VacuumTensor.superfunctor (W β) (probeOldVacuumObject D Sc m)).toFunctor

private instance : (tensorOutputFunctor D Sc m cutoff L ΛR).Additive where
  map_add := funext fun β => (VacuumTensor.superfunctor (W β)
    (probeOldVacuumObject D Sc m)).toFunctor.map_add
private instance : (tensorOutputFunctor D Sc m cutoff L ΛR).Linear k where
  map_smul f r := funext fun β => (VacuumTensor.superfunctor (W β)
    (probeOldVacuumObject D Sc m)).toFunctor.map_smul r f
private instance : IsSuperfunctor k (tensorOutputFunctor D Sc m cutoff L ΛR) where
  map_mem hf β := IsSuperfunctor.map_mem
    (F := (VacuumTensor.superfunctor (W β) (probeOldVacuumObject D Sc m)).toFunctor) hf

/-- Tensor with the full chosen reservoir family before empty-probe evaluation. -/
def tensorOutput : ProbeVacuumCap.modulePiCategory D Sc m ⟶
    elvWeightSpace D Sc cutoff bound ΛR (ReservoirWord.weight D ΛR 0) :=
  ⟨tensorOutputFunctor D Sc m cutoff L ΛR⟩

omit [Fintype I] in
/-- The empty reservoir word has its prescribed original weight. -/
theorem reservoirWeight_empty : ReservoirWord.weight D ΛR 0 = -ΛR := by
  simp [ReservoirWord.weight]

/-- The same full tensor output, at the weight used by the native bend chart. -/
def tensorOutputAt : ProbeVacuumCap.modulePiCategory D Sc m ⟶
    elvWeightSpace D Sc cutoff bound ΛR (-ΛR) :=
  reservoirWeight_empty D ΛR ▸ tensorOutput D Sc m cutoff L ΛR

private theorem output_cast_block
    {A : PiSCat.{u,u,u+1} k} {x y : X} (h : x = y)
    (F : A ⟶ elvWeightSpace D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR x)
    (δ : WeightBlocks D ΛR y) :
    (show A ⟶ elvWeightSpace D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR y from
      h ▸ F).comp (elvBlockEval D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR δ) =
      F.comp (elvBlockEval D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR
        ⟨δ.1, δ.2.trans h.symm⟩) := by
  subst y
  rfl

/-- The selected block is the native tensor functor used by the moment maps. -/
theorem tensorOutputAt_empty :
    (tensorOutputAt D Sc m cutoff L ΛR).comp
        (elvBlockEval D Sc cutoff bound ΛR (emptyBlock D ΛR)) =
      VacuumTensor.probeFunctor D Sc m cutoff bound
        ((BalancedInduction.restriction (contentInclusion D Sc cutoff bound (0 : Multiset I))).obj
          (PowerVacuumCoefficient.weightedVacuum D Sc cutoff L)) := by
  rw [tensorOutputAt, output_cast_block]
  rfl

variable (ΛP : X)

private theorem comp_cast_heq
    {x y : X} (h : x = y)
    (G : ProbeVacuumCap.modulePiCategory D Sc m ⟶ elvWeightSpace D Sc cutoff bound ΛR x) :
    HEq ((emptyProbe D Sc m ΛP).comp
      (show ProbeVacuumCap.modulePiCategory D Sc m ⟶ elvWeightSpace D Sc cutoff bound ΛR y from
        h ▸ G)) ((emptyProbe D Sc m ΛP).comp G) := by
  subst y
  rfl

private theorem input_cast_heq
    {x y z : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR z) :
    HEq (show probeOldWeightSpace D Sc m ΛP y ⟶ elvWeightSpace D Sc cutoff bound ΛR z from
      h ▸ F) F := by
  subst y
  rfl

omit [Fintype I] in
private theorem homWeight_inverse_obj_heq
    (TT WW : SKM.RouquierFamily (k := k) (B := PiSCat.{u,u,u+1} k) D)
    {a a' b b' : X} (ha : a = a') (hb : b = b')
    (Z : SKM.homWeightSector TT.obj WW.obj a' b') :
    HEq ((SKM.homWeightEquivalence TT WW ha hb).inverse.obj Z) Z := by
  subst a'
  subst b'
  rfl

variable
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "T" => probeOldRouquierFamily D (parameterTwist D Sc) m ΛP hcP
local notation "R" => elvRouquierFamily D (parameterTwist D Sc) cutoff bound ΛR hcR

private theorem probeWeight_zero : (P).muP (0,0) = ΛP := by
  simp [ProbeReservoir.muP, elvProbeReservoir]
private theorem reservoirWeight_zero : (P).muM (0,0) = -ΛR := by
  simp [ProbeReservoir.muM, elvProbeReservoir]

/-- The full tensor input in the precise weight presentations of the padded bend. -/
def tensorSectorInput : (P).H (0,0) :=
  (SKM.homWeightEquivalence T R
    (probeWeight_zero D Sc m cutoff L ΛR ΛP hcP hcR)
    (reservoirWeight_zero D Sc m cutoff L ΛR ΛP hcP hcR)).inverse.obj
      (preCapInput D (parameterTwist D Sc) m ΛP hcP
        (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR)
          (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR))

/-- Both presentations retain the same selected supported tensor Hom. -/
theorem tensorSectorInput_eq_supported :
    tensorSectorInput D Sc m cutoff L ΛR ΛP hcP hcR =
      (SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR).obj := by
  apply eq_of_heq
  have h₁ := homWeight_inverse_obj_heq D T R
    (probeWeight_zero D Sc m cutoff L ΛR ΛP hcP hcR)
    (reservoirWeight_zero D Sc m cutoff L ΛR ΛP hcP hcR)
    (preCapInput D (parameterTwist D Sc) m ΛP hcP
      (elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR) (-ΛR)
        (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR))
  have h₂ := comp_cast_heq D (parameterTwist D Sc) m cutoff L ΛR ΛP
    (reservoirWeight_empty D ΛR)
    (tensorOutput D (parameterTwist D Sc) m cutoff L ΛR)
  have h₃ : HEq (SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR).obj
      (selectedHom D (parameterTwist D Sc) m cutoff ΛP ΛR L) := by
    rw [SupportedSectors.tensorVacuum_obj]
    unfold SupportedSectors.tensorHomAt
    exact input_cast_heq D (parameterTwist D Sc) m cutoff L ΛR ΛP
      (SupportedSectors.probeWeight_vacuum D ΛP).symm _
  exact (h₁.trans h₂).trans h₃.symm

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
