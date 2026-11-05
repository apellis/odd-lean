import OddMath.QuiverHecke.CyclotomicAction.ELVContentHomClosure

/-! # The selected tensor vacuum has exact formal support

The initial object of F4/(A1) in `SwappedActionAssembly.md` is the already
chosen whole-weight `WeightTensorVacuum.selectedHom`, on every input and
all collision blocks. Its support is proved from its construction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ContentHomSupport
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
  (cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)

private def forgetEmptyFunctor (ν : List I) (h : ν = []) :
    ProbeEvaluatedModules D Sc m ν ⥤
      Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k) := by
  subst ν
  exact ObjectProperty.ι _
private instance (ν : List I) (h : ν = []) : (forgetEmptyFunctor D Sc m ν h).Additive := by
  subst ν
  exact ⟨by intros; rfl⟩
private instance (ν : List I) (h : ν = []) : (forgetEmptyFunctor D Sc m ν h).Linear k := by
  subst ν
  exact ⟨fun _ _ => rfl⟩
private instance (ν : List I) (h : ν = []) : IsSuperfunctor k (forgetEmptyFunctor D Sc m ν h) := by
  subst ν
  exact ⟨fun hf => hf⟩

/-- Formal reservoir content zero at its literal chosen weight. -/
def reservoirVacuumBlock : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0) :=
  ⟨0, by simp [blockWeight, ReservoirWord.weight]⟩

/-- The exact-content tensor functor whose whole-weight realization is the selected vacuum. -/
def vacuumHom : Hom D Sc m cutoff (PowerWordContent.powerBound D cutoff L)
    (WeightTensorVacuum.emptyBlock D ΛP) (reservoirVacuumBlock D ΛR) :=
  (show Superfunctor k (ProbeCanonicalModules D Sc m (0 : Multiset I))
    (Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k)) from
      ⟨forgetEmptyFunctor D Sc m _ Multiset.toList_zero⟩).comp
    (VacuumTensor.superfunctor
      ((ReservoirWordValue.initialValue D ΛR Sc cutoff L) (reservoirVacuumBlock D ΛR))
      (probeOldVacuumObject D Sc m))

/-- The selected component equality holds as a whole Superfunctor, on all maps. -/
theorem selectedVacuum_component :
    (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L).comp
      (elvBlockEval D Sc cutoff (PowerWordContent.powerBound D cutoff L) ΛR
        (reservoirVacuumBlock D ΛR)) =
    (probeOldBlockEval D Sc m ΛP (WeightTensorVacuum.emptyBlock D ΛP)).comp
      (vacuumHom D Sc m cutoff ΛP ΛR L) := by
  rfl

private theorem tensor_isZero {C : Type u} [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] (W : Superfunctor k C (SVec k))
    (hW : Limits.IsZero W) (V : SVec k) : Limits.IsZero (VacuumTensor.object W V) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  have he := (Limits.IsZero.iff_id_eq_zero W).mp hW
  apply Superfunctor.hom_ext_parity
  · intro c
    have hc : (𝟙 (W.obj c) : End (W.obj c)) = 0 := congrArg (fun f : End W => f.app 0 c) he
    change (𝟙 (SVec.tensorObj (W.obj c) V) : End _) = 0
    rw [← SVec.whiskerRight_id, hc, SVec.whiskerRight_zero]
  · intro c
    rfl

/-- Every nonzero-content output of the literal selected Hom is zero,
for every input, including other blocks of the same original weight. -/
theorem selectedVacuum_off_isZero
    (M : ProbeOldWeightProduct D Sc m ΛP (-ΛP))
    (δ : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (hδ : δ ≠ reservoirVacuumBlock D ΛR) :
    Limits.IsZero (((WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L).obj M) δ) := by
  have hd : δ.1 ≠ (0 : Multiset I) := fun he => hδ (Subtype.ext he)
  change Limits.IsZero (VacuumTensor.object
    ((ReservoirWordValue.initialValue D ΛR Sc cutoff L) δ)
    (((WeightTensorVacuum.emptyProbe D Sc m ΛP).obj M).obj (probeOldVacuumObject D Sc m)))
  apply tensor_isZero
  exact PowerWordWeight.wordAt_isZero D Sc cutoff L [] δ.1 hd

/-- The actual selected Hom belongs to the replete exact-content category,
without an assumed comparison or a regular-input-only support assertion. -/
theorem selectedVacuum_supported :
    Supported D Sc m cutoff (PowerWordContent.powerBound D cutoff L)
      (WeightTensorVacuum.emptyBlock D ΛP) (reservoirVacuumBlock D ΛR)
      (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L) :=
  supported_of_selected D Sc m cutoff (PowerWordContent.powerBound D cutoff L)
    (WeightTensorVacuum.emptyBlock D ΛP) (reservoirVacuumBlock D ΛR)
    (WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L)
    (vacuumHom D Sc m cutoff ΛP ΛR L)
    (selectedVacuum_component D Sc m cutoff ΛP ΛR L)
    (fun M δ hδ => selectedVacuum_off_isZero D Sc m cutoff ΛP ΛR L M δ hδ)

end OddMath.QuiverHecke.ELVOld.ContentHomSupport
