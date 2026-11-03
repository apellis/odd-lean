import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport

/-! # An occupied vacuum probe append unit

The positive-level probe in `SwappedVacuumBubbles.md`, §1, is tested on
its canonical nonzero empty vector. The existing inverse unit matrix
splits the append unit; no new polynomial quotient presentation is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
namespace OddMath.QuiverHecke
universe u
private theorem linearEquiv_apply_ne_zero
    {k V W : Type u} [CommRing k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (z : V) (hz : z ≠ 0) : e z ≠ 0 := by
  intro h
  exact hz (e.injective (h.trans e.map_zero.symm))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- At positive cutoff the ordinary append unit on the empty old component
is split by slot zero of the prescribed inverse unit matrix. -/
theorem oldVacuumInductionUnit_injective
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (i : I) (hi : 0 < cutoff i) :
    Function.Injective (unit (append D Sc cutoff i) M.toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)) := by
  let t : OldCategory D Sc cutoff := ⟨[]⟩
  have hh : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
    simp [contentCrossingHeight]
  let r : Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)) :=
    ⟨0, by rw [VacuumCoefficient.count]; exact hi⟩
  have hl (z : M.obj t) : moduleUnitCoefficient D Sc cutoff M i t hh r
      (unit (append D Sc cutoff i) M.toFunctor t z) = z := by
    have h := moduleUnitCoefficient_dot_window D Sc cutoff M i t hh r 0
      (by rw [VacuumCoefficient.count]; exact hi) z
    change moduleUnitCoefficient D Sc cutoff M i t hh r
      ((((adjunction (append D Sc cutoff i)).unit.app M).total t) z) = z at h
    change moduleUnitCoefficient D Sc cutoff M i t hh r
      (((adjunctionUnit (append D Sc cutoff i)).app M).total t z) = z at h
    rw [adjunctionUnit_total_apply D Sc cutoff i M t z] at h
    exact h
  exact Function.LeftInverse.injective hl

/-- The native empty-content append unit is injective. Its selected comparison
with the full old extension retains the two literal adjunction units. -/
theorem oldContentVacuumInductionUnit_injective
    (M : Superfunctor k (OldContentCategory D Sc cutoff []) (SVec k))
    (i : I) (hi : 0 < cutoff i) (s : OldContentCategory D Sc cutoff []) :
    Function.Injective (unit (oldContentAppend D Sc cutoff [] i) M.toFunctor s) := by
  rcases s with ⟨⟨word⟩, hw⟩
  have he : word = [] := List.perm_nil.mp hw
  subst word
  let s : OldContentCategory D Sc cutoff [] := ⟨⟨[]⟩, hw⟩
  let J := oldContentInclusion D Sc cutoff []
  let L := induced J M
  intro x y hxy
  change unit (oldContentAppend D Sc cutoff [] i) M.toFunctor s x =
    unit (oldContentAppend D Sc cutoff [] i) M.toFunctor s y at hxy
  have h := congrArg (oldContentAppendRestrictionLinear D Sc cutoff [] i M
    ((oldContentAppend D Sc cutoff [] i).obj s)) hxy
  have hx' := oldContentAppendRestrictionIso_unit D Sc cutoff [] i M s x
  have hy' := oldContentAppendRestrictionIso_unit D Sc cutoff [] i M s y
  have hu : unit (append D Sc cutoff i) L.toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      (unit J M.toFunctor s x) =
      unit (append D Sc cutoff i) L.toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
        (unit J M.toFunctor s y) := by
    dsimp only [L, J, s, induced, moduleFunctor, oldContentAppend] at h hx' hy' ⊢
    have h0 := hx'.symm.trans (h.trans hy')
    exact h0
  have heq := oldVacuumInductionUnit_injective D Sc cutoff L i hi hu
  have hh := congrArg (fullyFaithfulUnitInverse J M.toFunctor s) heq
  have hx := LinearMap.congr_fun (fullyFaithfulUnitInverse_unit J M.toFunctor s) x
  have hy := LinearMap.congr_fun (fullyFaithfulUnitInverse_unit J M.toFunctor s) y
  exact hx.symm.trans (hh.trans hy)

private theorem appendLinearEquiv_unit (m : I → ℕ) (ν : List I)
    (R : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hR : ProbeEvaluatesCoefficients D m Sc ν R) (i : I)
    (v : OldContentCategory D Sc (probeCutoff D m) ν) (b : R.obj v) :
    probeAppendLinearEquiv D Sc m ν R hR i ((oldContentAppend D Sc (probeCutoff D m) ν i).obj v)
      (unit (oldContentAppend D Sc (probeCutoff D m) ν i) R.toFunctor v b) =
    unit (probeOrdinaryAppend D Sc m ν i)
      (probeOrdinaryModuleSuperfunctor D Sc m ν R hR).toFunctor
      ((probeOldOrdinaryFunctor D Sc m ν).obj v) b := by
  change (probeAppendLinearEquiv D Sc m ν R hR i
    ((oldContentAppend D Sc (probeCutoff D m) ν i).obj v)).toLinearMap _ = _
  rw [probeAppendLinearEquiv_hom]
  exact probeAppendOrdinaryModuleIso_hom_unit D Sc m ν R hR i v b

variable [Fintype I] (m : I → ℕ)

omit [Fintype I] in
private theorem probeCutoff_pos (i : I) (hi : 0 < m i) : 0 < probeCutoff D m i := by
  change 0 < probeDotExponent D i * m i
  apply Nat.mul_pos _ hi
  unfold probeDotExponent
  split_ifs <;> decide

/-- The actual regular probe vacuum satisfies the required scalar-evaluation property. -/
theorem probeOldVacuumRegular_evaluates :
    ProbeEvaluatesCoefficients D m Sc [] (probeOldVacuumRegular D Sc m) :=
  probeOldModule_evaluatesCoefficients D m Sc [] _

/-- The ordinary probe vacuum is the proved scalar descent of the same regular module. -/
abbrev probeOrdinaryVacuumRegular :=
  probeOrdinaryModuleSuperfunctor D Sc m [] (probeOldVacuumRegular D Sc m)
    (probeOldVacuumRegular_evaluates D Sc m)

/-- The actual old one-letter target of append from the empty regular probe. -/
abbrev probeOldVacuumAppendTarget (i : I) :=
  (oldContentAppend D Sc (probeCutoff D m) [] i).obj (probeOldVacuumObject D Sc m)

/-- The same word in the literal ordinary probe category. -/
abbrev probeOrdinaryVacuumAppendTarget (i : I) :=
  (probeOldOrdinaryFunctor D Sc m [i]).obj (probeOldVacuumAppendTarget D Sc m i)

/-- The native append unit applied to the nonzero regular empty vector. -/
def probeOldVacuumAppendVector (i : I) :
    Obj (oldContentAppend D Sc (probeCutoff D m) [] i)
      (probeOldVacuumRegular D Sc m).toFunctor (probeOldVacuumAppendTarget D Sc m i) :=
  unit (oldContentAppend D Sc (probeCutoff D m) [] i)
    (probeOldVacuumRegular D Sc m).toFunctor (probeOldVacuumObject D Sc m)
      (probeOldVacuumVector D Sc m)

/-- The prescribed old probe append coend is occupied at every positive probe level. -/
theorem probeOldVacuumAppendVector_ne_zero [Nontrivial k] (i : I) (hi : 0 < m i) :
    probeOldVacuumAppendVector D Sc m i ≠ 0 := by
  intro hz
  have h := oldContentVacuumInductionUnit_injective D Sc (probeCutoff D m)
    (probeOldVacuumRegular D Sc m) i (probeCutoff_pos D m i hi) (probeOldVacuumObject D Sc m)
    (hz.trans (map_zero (unit (oldContentAppend D Sc (probeCutoff D m) [] i)
      (probeOldVacuumRegular D Sc m).toFunctor (probeOldVacuumObject D Sc m))).symm)
  exact probeOldVacuumVector_ne_zero D Sc m h

/-- The same vector transported by the specified invertible scalar append chart. -/
def probeOrdinaryVacuumAppendVector (i : I) :
    Obj (probeOrdinaryAppend D Sc m [] i) (probeOrdinaryVacuumRegular D Sc m).toFunctor
      (probeOrdinaryVacuumAppendTarget D Sc m i) :=
  probeAppendLinearEquiv D Sc m [] (probeOldVacuumRegular D Sc m)
    (probeOldVacuumRegular_evaluates D Sc m) i (probeOldVacuumAppendTarget D Sc m i)
      (probeOldVacuumAppendVector D Sc m i)

/-- The transported vector remains nonzero in the actual ordinary coend. -/
theorem probeOrdinaryVacuumAppendVector_ne_zero [Nontrivial k] (i : I) (hi : 0 < m i) :
    probeOrdinaryVacuumAppendVector D Sc m i ≠ 0 := by
  change probeAppendLinearEquiv D Sc m [] (probeOldVacuumRegular D Sc m)
    (probeOldVacuumRegular_evaluates D Sc m) i (probeOldVacuumAppendTarget D Sc m i)
      (probeOldVacuumAppendVector D Sc m i) ≠ 0
  exact linearEquiv_apply_ne_zero _ _ (probeOldVacuumAppendVector_ne_zero D Sc m i hi)

/-- The chosen scalar chart identifies the vector with the literal ordinary append unit. -/
theorem probeOrdinaryVacuumAppendVector_eq_unit (i : I) :
    probeOrdinaryVacuumAppendVector D Sc m i =
      unit (probeOrdinaryAppend D Sc m [] i) (probeOrdinaryVacuumRegular D Sc m).toFunctor
        ((probeOldOrdinaryFunctor D Sc m []).obj (probeOldVacuumObject D Sc m))
          (probeOldVacuumVector D Sc m) := by
  dsimp only [probeOrdinaryVacuumAppendVector, probeOldVacuumAppendVector,
    probeOldVacuumAppendTarget, probeOrdinaryVacuumRegular]
  exact appendLinearEquiv_unit D Sc m [] (probeOldVacuumRegular D Sc m)
    (probeOldVacuumRegular_evaluates D Sc m) i (probeOldVacuumObject D Sc m)
      (probeOldVacuumVector D Sc m)

end OddMath.QuiverHecke
