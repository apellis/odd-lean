import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapModuleWindow
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCapNaturality
import OddMath.SKM.RouquierHomContent

/-! # Precomposition by the prescribed probe cap

`SwappedActionAssembly.md`, §5 (A14) and §6, uses the homogeneous native
cap on a Hom sector. We retain the actual inverse-defined cap and the same
module dot. The lower Hom construction does not require a Rouquier family;
identification with its normalized left adjunction still requires its unit
and triangles.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem homPreTransform_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} {p : ZMod 2} (η : F ⟶ G)
    (hη : η ∈ parity (R := k) _ _ p) (H : B ⟶ R) :
    (SKM.homPreTransform (c := R) η hη).total H = η ▷ H := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, SKM.homPreTransform]

private theorem whiskerRight_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

private theorem restrictedDot_supernatural
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α) :
    IsSupernatural k p (F := induction J ⋙ restriction J) (G := induction J ⋙ restriction J)
      (fun M => restrictedDotEnd J hα M) :=
  (transformComponent_supernatural hα).whiskerRight (restriction J)

private theorem family_total
    {k : Type u} [CommRing k] {C A : Type*} [Category C] [Category A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} {p : ZMod 2} {α : ∀ M, F.obj M ⟶ G.obj M}
    (hα : IsSupernatural k p α) (M : C) : hα.toSuperNatTrans.total M = α M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The native module category of the original empty-content probe, with
its given vector-parity shift. -/
def modulePiCategory : PiSCat.{u,u,u+1} k where
  toSCat := SCat.of k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
  pi := supermodulePiSupercategory

/-- The actual F/E endofunctor on the probe input category. -/
def appendRestrict (i : I) : modulePiCategory D Sc m ⟶ modulePiCategory D Sc m :=
  show Superfunctor k
    (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
    (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) from
      ⟨induction (K i) ⋙ restriction (K i)⟩

private def lastSlot (i : I) (hP : 0 < cut i) :
    Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
  ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩

omit [Fintype I] in
private theorem height (i : I) : 0 ≤ contentCrossingHeight D cut i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

/-- The input-supernatural last inverse row, as a genuine 2-cell in the
native Π-supercategory of module categories. -/
def capCell (i : I) (hP : 0 < cut i) :
    appendRestrict D Sc m i ⟶ 𝟙 (modulePiCategory D Sc m) :=
  contentCoefficientCapFamily D Sc cut [] i (height D m i) (lastSlot D m i hP)

omit [Fintype I] in
/-- The cap 2-cell retains the prescribed last-row degree. -/
theorem capCell_mem (i : I) (hP : 0 < cut i) :
    capCell D Sc m i hP ∈ parity (R := k) _ _ ((cut i - 1) • D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (contentCoefficientCapFamily_isHomogeneous D Sc cut [] i
      (height D m i) (lastSlot D m i hP))

/-- Its component at the regular probe is the already normalized cap. -/
theorem capCell_total (i : I) (hP : 0 < cut i) :
    (capCell D Sc m i hP).total N = cap D Sc m i hP :=
  contentCoefficientCapFamily_total D Sc cut [] i
    (height D m i) (lastSlot D m i hP) N

/-- Precomposition by the actual cap, with signed naturality on every
reservoir functor and arbitrary homogeneous maps between such functors. -/
def preCap (R : PiSCat.{u,u,u+1} k) (i : I) (hP : 0 < cut i) :
    SuperNatTrans k (SKM.homPre (k := k) (c := R) (appendRestrict D Sc m i))
      (SKM.homPre (k := k) (c := R) (𝟙 (modulePiCategory D Sc m))) :=
  SKM.homPreTransform (k := k) (B := PiSCat.{u,u,u+1} k) (capCell D Sc m i hP) (capCell_mem D Sc m i hP)

/-- The actual restricted induction dot as an input-supernatural 2-cell. -/
def dotCell (i : I) : End (appendRestrict D Sc m i) :=
  (restrictedDot_supernatural (K i)
    (probeOldContentAppendDot_supernatural D Sc m [] i)).toSuperNatTrans

omit [Fintype I] in
/-- The dot 2-cell has precisely the moving-colour degree. -/
theorem dotCell_mem (i : I) : dotCell D Sc m i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    ((restrictedDot_supernatural (K i)
      (probeOldContentAppendDot_supernatural D Sc m [] i)).toSuperNatTrans_isHomogeneous)

/-- Its regular-probe component is the same module dot as the cap window. -/
theorem dotCell_total (i : I) : (dotCell D Sc m i).total N = moduleDot D Sc m i := by
  exact family_total (restrictedDot_supernatural (K i)
    (probeOldContentAppendDot_supernatural D Sc m [] i)) N

/-- The genuine precomposition dot transformation on the chosen Hom carrier. -/
def preDot (R : PiSCat.{u,u,u+1} k) (i : I) :
    SuperNatTrans k (SKM.homPre (k := k) (c := R) (appendRestrict D Sc m i))
      (SKM.homPre (k := k) (c := R) (appendRestrict D Sc m i)) :=
  SKM.homPreTransform (k := k) (B := PiSCat.{u,u,u+1} k)
    (dotCell D Sc m i) (dotCell_mem D Sc m i)

/-- Evaluating the precomposition dot gives the reservoir image of the
same signed module dot, with no transpose substitution. -/
theorem preDot_total (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    ((preDot D Sc m R i).total H).total N = H.map (moduleDot D Sc m i) := by
  rw [preDot, homPreTransform_total, whiskerRight_total, dotCell_total]

/-- Evaluation of the given Hom dot, with its endomorphism object explicit. -/
def preDotEnd (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) : End (H.obj (source D Sc m i)) :=
  ((preDot D Sc m R i).total H).total N

/-- This evaluated endomorphism is the image of the same module dot. -/
theorem preDotEnd_eq (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    preDotEnd D Sc m R i H = H.map (moduleDot D Sc m i) :=
  preDot_total D Sc m R i H

/-- The polynomial is preserved on the evaluated, actual precomposition
dot in the same Hom carrier as the prescribed cap. -/
theorem preDot_odd_polynomial (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 1)
    (H : modulePiCategory D Sc m ⟶ R) :
    (preDotEnd D Sc m R i H ^ 2 + 1) ^ m i = 0 := by
  rw [preDotEnd_eq]
  exact additiveFunctor_odd_probe_polynomial H.toFunctor (moduleDot D Sc m i) (m i)
    (moduleDot_odd_polynomial D Sc m i hi)

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
