import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVOperatorPowerComparison

/-! # Ground-valued inverse rows on the regular probe

The probe side of `SwappedVacuumNonpositiveBubbles.md`, §2, requires a
last inverse unit-matrix row with ground-valued target. We specialize the
prescribed old inverse row to the regular probe, using its literal empty
scalar coordinate and the selected content append comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCoefficient
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
private theorem inductionDotPower_intertwine
    {k C A W : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [AddCommMonoid W] [Module k W]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : A)
    (R : Obj J M.toFunctor w →ₗ[k] W) (e : Module.End k W)
    (hd : R ∘ₗ transformLinear hα M w = e ∘ₗ R) (n : ℕ)
    (x : Obj J M.toFunctor w) :
    R (((transformLinear hα M w : Module.End k (Obj J M.toFunctor w)) ^ n) x) =
      (e ^ n) (R x) :=
  LinearMap.congr_fun (intertwine_pow _ _ _ hd n) x

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "M" => probeOldVacuumRegular D Sc m
local notation "s" => probeOldVacuumObject D Sc m
local notation "J" => oldContentInclusion D Sc cut []
local notation "L" => induced J M
local notation "t" => OldContentCategory.obj (probeOldVacuumObject D Sc m)


private def contentAppendUnit
    (N : Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
    (i : I) (v : OldContentCategory D Sc cut []) (u : k →ₗ[k] N.obj v) :
    k →ₗ[k] Obj (oldContentAppend D Sc cut [] i) N.toFunctor
      ((oldContentAppend D Sc cut [] i).obj v) :=
  (unit (oldContentAppend D Sc cut [] i) N.toFunctor v).comp u

private def contentAppendDot
    (N : Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
    (i : I) (v : OldContentCategory D Sc cut []) :
    Module.End k (Obj (oldContentAppend D Sc cut [] i) N.toFunctor
      ((oldContentAppend D Sc cut [] i).obj v)) :=
  transformLinear (oldContentAppendDot_supernatural D Sc cut [] i) N
    ((oldContentAppend D Sc cut [] i).obj v)

private def contentFunctional
    (N : Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
    (i : I) (v : OldContentCategory D Sc cut [])
    (row : mateTargetSpace D Sc cut i (induced J N) v.obj →ₗ[k] k) :
    Obj (oldContentAppend D Sc cut [] i) N.toFunctor
      ((oldContentAppend D Sc cut [] i).obj v) →ₗ[k] k where
  toFun z := row (oldContentAppendRestrictionLinear D Sc cut [] i N
    ((oldContentAppend D Sc cut [] i).obj v) z)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c x := by rw [map_smul, map_smul]; rfl

omit [Fintype I] in
private theorem contentRow_dot_window
    (N : Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
    (i : I) (v : OldContentCategory D Sc cut [])
    (u : k →ₗ[k] N.obj v)
    (row : mateTargetSpace D Sc cut i (induced J N) v.obj →ₗ[k] k)
    (a : ℕ) (c expected : k)
    (hrow : row
      (((actualInductionDot D Sc cut i (induced J N) ((append D Sc cut i).obj v.obj) :
          Module.End k (mateTargetSpace D Sc cut i (induced J N) v.obj)) ^ a)
        (unit (append D Sc cut i) (induced J N).toFunctor v.obj (unit J N.toFunctor v (u c)))) = expected) :
    contentFunctional D Sc m N i v row
      ((contentAppendDot D Sc m N i v ^ a) (contentAppendUnit D Sc m N i v u c)) = expected := by
  dsimp only [contentFunctional, contentAppendDot, contentAppendUnit, LinearMap.comp_apply]
  let R : Obj (oldContentAppend D Sc cut [] i) N.toFunctor
      ((oldContentAppend D Sc cut [] i).obj v) →ₗ[k]
      mateTargetSpace D Sc cut i (induced J N) v.obj :=
    oldContentAppendRestrictionLinear D Sc cut [] i N ((oldContentAppend D Sc cut [] i).obj v)
  let g : Module.End k (mateTargetSpace D Sc cut i (induced J N) v.obj) :=
    actualInductionDot D Sc cut i (induced J N) ((append D Sc cut i).obj v.obj)
  have hd := oldContentAppendRestrictionIso_dot D Sc cut [] i N
    ((oldContentAppend D Sc cut [] i).obj v)
  change R.comp (transformLinear (oldContentAppendDot_supernatural D Sc cut [] i) N
    ((oldContentAppend D Sc cut [] i).obj v)) = g.comp R at hd
  have hp := inductionDotPower_intertwine (oldContentAppend D Sc cut [] i)
    (oldContentAppendDot_supernatural D Sc cut [] i) N
    ((oldContentAppend D Sc cut [] i).obj v) R g hd a
    (unit (oldContentAppend D Sc cut [] i) N.toFunctor v (u c))
  have hu := oldContentAppendRestrictionIso_unit D Sc cut [] i N v (u c)
  change R (unit (oldContentAppend D Sc cut [] i) N.toFunctor v (u c)) =
    unit (append D Sc cut i) (induced J N).toFunctor v.obj (unit J N.toFunctor v (u c)) at hu
  have hunit := congrArg (fun x => (g ^ a) x) hu
  have hraw := hp.trans hunit
  dsimp only [g, R] at hraw
  exact (congrArg row hraw).trans hrow

omit [Fintype I] in
private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cut i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topSlot (i : I) (hN : 0 < cut i) :
    Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
  ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- Scalar insertion into the canonical full old extension of the regular probe. -/
def scalarUnit : k →ₗ[k] (L).obj t :=
  (unit J (M).toFunctor s).comp (probeVacuumScalarEquiv D Sc m).toLinearMap

/-- Decode the same empty component, using the inverse of the prescribed
fully faithful inclusion unit and the original empty scalar coordinate. -/
def scalarCoordinate : (L).obj t →ₗ[k] k :=
  (probeVacuumScalarEquiv D Sc m).symm.toLinearMap.comp
    (fullyFaithfulUnitInverse J (M).toFunctor s)

/-- The two empty-coordinate maps retain the original scalar normalization. -/
theorem scalarCoordinate_unit (c : k) :
    scalarCoordinate D Sc m (scalarUnit D Sc m c) = c := by
  have h := LinearMap.congr_fun (fullyFaithfulUnitInverse_unit J (M).toFunctor s)
    (probeVacuumScalarEquiv D Sc m c)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  change (probeVacuumScalarEquiv D Sc m).symm
    (fullyFaithfulUnitInverse J (M).toFunctor s
      (unit J (M).toFunctor s (probeVacuumScalarEquiv D Sc m c))) = c
  rw [h]
  exact (probeVacuumScalarEquiv D Sc m).symm_apply_apply c

/-- The literal last old inverse row with its output decoded in the ground ring. -/
def extensionFunctional (i : I) (hN : 0 < cut i) :
    mateTargetSpace D Sc cut i L t →ₗ[k] k :=
  (scalarCoordinate D Sc m).comp
    (moduleUnitCoefficient D Sc cut L i t (height D m i) (topSlot D m i hN))

/-- The prescribed extraction window, on every scalar input, before
restricting to fixed content. -/
theorem extensionFunctional_dot_window (i : I) (hN : 0 < cut i)
    (a : ℕ) (ha : a < cut i) (c : k) :
    extensionFunctional D Sc m i hN
      (((actualInductionDot D Sc cut i L ((append D Sc cut i).obj t)) ^ a)
        (unit (append D Sc cut i) (L).toFunctor t (scalarUnit D Sc m c))) =
      if a + 1 = cut i then c else 0 := by
  have h := moduleUnitCoefficient_dot_window D Sc cut L i t (height D m i)
    (topSlot D m i hN) a (by
      change a < contentUnitCount D cut i (([] : List I) : Multiset I)
      simpa only [VacuumCoefficient.count] using ha)
    (scalarUnit D Sc m c)
  change moduleUnitCoefficient D Sc cut L i t (height D m i) (topSlot D m i hN)
    (((actualInductionDot D Sc cut i L ((append D Sc cut i).obj t)) ^ a)
      ((((adjunctionUnit (append D Sc cut i)).app L).total t) (scalarUnit D Sc m c))) =
    if a = (topSlot D m i hN).val then scalarUnit D Sc m c else 0 at h
  rw [adjunctionUnit_total_apply] at h
  change moduleUnitCoefficient D Sc cut L i t (height D m i) (topSlot D m i hN)
    (((actualInductionDot D Sc cut i L ((append D Sc cut i).obj t)) ^ a)
      (unit (append D Sc cut i) (L).toFunctor t (scalarUnit D Sc m c))) =
    if a = cut i - 1 then scalarUnit D Sc m c else 0 at h
  change scalarCoordinate D Sc m _ = _
  rw [h]
  have he : (a = cut i - 1) ↔ a + 1 = cut i := by omega
  by_cases hh : a + 1 = cut i
  · rw [ite_eq_left (he.mpr hh), ite_eq_left hh, scalarCoordinate_unit]
  · rw [ite_eq_right (fun hEq => hh (he.mp hEq)), ite_eq_right hh, map_zero]

/-- The native content append coend of the prescribed regular probe. -/
abbrev appendSpace (i : I) :=
  Obj (oldContentAppend D Sc cut [] i) (M).toFunctor (probeOldVacuumAppendTarget D Sc m i)

/-- The ordinary append unit with scalar input in the original empty coordinate. -/
def appendUnit (i : I) : k →ₗ[k] appendSpace D Sc m i :=
  contentAppendUnit D Sc m M i s (probeVacuumScalarEquiv D Sc m).toLinearMap

/-- The literal signed right dot on the same native probe append coend. -/
def appendDot (i : I) : Module.End k (appendSpace D Sc m i) :=
  contentAppendDot D Sc m M i s

/-- The selected content chart specializes the prescribed inverse row to
the native probe coend, without an input coefficient-extraction assumption. -/
def functional (i : I) (hN : 0 < cut i) : appendSpace D Sc m i →ₗ[k] k :=
  contentFunctional D Sc m M i s (extensionFunctional D Sc m i hN)

/-- The ground-valued last inverse row has its exact top-degree window
on the native signed probe dot and the original append unit. -/
theorem functional_dot_window (i : I) (hN : 0 < cut i)
    (a : ℕ) (ha : a < cut i) (c : k) :
    functional D Sc m i hN ((appendDot D Sc m i ^ a) (appendUnit D Sc m i c)) =
      if a + 1 = cut i then c else 0 := by
  have hrow := extensionFunctional_dot_window D Sc m i hN a ha c
  have h := contentRow_dot_window D Sc m M i s
    (probeVacuumScalarEquiv D Sc m).toLinearMap (extensionFunctional D Sc m i hN)
    a c (if a + 1 = cut i then c else 0) hrow
  simpa only [functional, appendDot, appendUnit] using h

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCoefficient
