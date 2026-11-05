import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPreCoordinates

/-! # Koszul signs of the probe dot in shifted precomposition coordinates

The dot in `SwappedActionAssembly.md`, §5 (A14), acts before removal of
the source parity shift. Super-interchange supplies its power signs. The
same probe polynomial survives this signed change of coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u
local instance probeCapPreDotHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def sourceIso {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    (E : A ⟶ B) (F : B ⟶ A) (H : A ⟶ R) (σ : ZMod 2) :=
  (SKM.homPre (k := k) E).mapIso ((SKM.homParityShiftDatum (k := k) σ).iso (F ≫ H)) ≪≫
    (associator E F H).symm

private theorem source_dot_sign {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    (E : A ⟶ B) (F : B ⟶ A) (H : A ⟶ R) (σ : ZMod 2)
    (x : End E) {p : ZMod 2} (hx : x ∈ parity (R := k) _ _ p) :
    (x ▷ (SKM.homParityShift (k := k) σ).obj (F ≫ H)) ≫ (sourceIso E F H σ).hom =
      koszulSign p σ • ((sourceIso E F H σ).hom ≫ ((x ▷ F) ▷ H)) := by
  simp only [sourceIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PiSCat.associator_inv]
  erw [Category.comp_id]
  exact TwoSupercategory.super_interchange hx
    ((SKM.homParityShiftDatum (k := k) σ).hom_mem (F ≫ H))

private theorem total_zsmul {k : Type u} [CommRing k] {A R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ R} (η : F ⟶ G) (z : ℤ) (M : A) :
    (z • η).total M = z • η.total M := by
  change z • η.app 0 M + z • η.app 1 M = z • (η.app 0 M + η.app 1 M)
  exact (smul_add _ _ _).symm

private theorem whisker_total {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

private theorem induction_dot_supernatural
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α) :
    IsSupernatural k p (F := induction J) (G := induction J) (fun M => dotEnd J hα M) :=
  transformComponent_supernatural hα

private theorem family_total {k : Type u} [CommRing k] {C A : Type*}
    [Category C] [Category A] [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} {p : ZMod 2} {α : ∀ M, F.obj M ⟶ G.obj M}
    (hα : IsSupernatural k p α) (M : C) : hα.toSuperNatTrans.total M = α M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

private theorem restriction_dotEnd
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (restriction J).map (dotEnd J hα M) = restrictedDotEnd J hα M := rfl

private theorem signed_conjugation {C : Type*} [Category C] [Preadditive C]
    {T S : C} (e : T ≅ S) (a : End T) (b : End S) (z : ℤ)
    (h : a ≫ e.hom = z • (e.hom ≫ b)) : a = z • (e.symm.conj b) := by
  have hh := congrArg (fun f => f ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Preadditive.zsmul_comp,
    Iso.conj_apply, Iso.symm_inv, Iso.symm_hom] using hh

private theorem signed_polynomial {A : Type*} [Ring A] (d : A) (p σ : ZMod 2) (n : ℕ)
    (h : (d ^ 2 + 1) ^ n = 0) : ((koszulSign p σ • d) ^ 2 + 1) ^ n = 0 := by
  rw [smul_pow, pow_two (koszulSign p σ), koszulSign_mul_self, one_smul]
  exact h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The original induction dot before any source parity comparison. -/
def inductionDotCell (i : I) : End (inductionCell D Sc m i) :=
  (induction_dot_supernatural (K i) (probeOldContentAppendDot_supernatural D Sc m [] i)).toSuperNatTrans

omit [Fintype I] in
/-- Its homogeneous degree is the moving-colour parity. -/
theorem inductionDotCell_mem (i : I) :
    inductionDotCell D Sc m i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (induction_dot_supernatural (K i)
      (probeOldContentAppendDot_supernatural D Sc m [] i)).toSuperNatTrans_isHomogeneous

/-- Its probe component is the given signed induction dot. -/
theorem inductionDotCell_total (i : I) :
    (inductionDotCell D Sc m i).total N =
      dotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N :=
  family_total (induction_dot_supernatural (K i)
    (probeOldContentAppendDot_supernatural D Sc m [] i)) N

/-- The literal raw pre-induction dot on the parity-shifted Hom source. -/
def shiftedPreDot (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) : End (shiftedPreSourceObject D Sc m R i H) :=
  ((inductionDotCell D Sc m i) ▷
    (SKM.homParityShift (k := k) ((cut i - 1) • D.parity i)).obj
      (restrictionCell D Sc m i ≫ H)).total N

/-- Passing the raw induction dot through the canonical source parity
comparison retains precisely its super-interchange sign. -/
theorem shiftedPreDot_coordinates (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    shiftedPreDot D Sc m R i H =
      koszulSign (D.parity i) ((cut i - 1) • D.parity i) •
        coordinatePreDotPower D Sc m R i H 1 := by
  have h := congrArg (fun η => η.total N)
    (source_dot_sign (inductionCell D Sc m i) (restrictionCell D Sc m i) H
      ((cut i - 1) • D.parity i) (inductionDotCell D Sc m i) (inductionDotCell_mem D Sc m i))
  rw [Superfunctor.comp_total, total_zsmul, Superfunctor.comp_total,
    whisker_total, whisker_total, whisker_total, inductionDotCell_total] at h
  have hr := restriction_dotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N
  change (restrictionCell D Sc m i).map _ = moduleDot D Sc m i at hr
  erw [hr] at h
  have hc := signed_conjugation (preSourceComponent D Sc m R i H)
    (shiftedPreDot D Sc m R i H) (preDotEnd D Sc m R i H)
    (koszulSign (D.parity i) ((cut i - 1) • D.parity i))
  rw [preDotEnd_eq] at hc
  have hraw : shiftedPreDot D Sc m R i H =
      ((SKM.homParityShift (k := k) ((cut i - 1) • D.parity i)).obj
        (restrictionCell D Sc m i ≫ H)).map
          (dotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N) := by
    rw [shiftedPreDot, whisker_total, inductionDotCell_total]
  have he : (preSourceComponent D Sc m R i H).hom =
      (sourceIso (inductionCell D Sc m i) (restrictionCell D Sc m i) H
        ((cut i - 1) • D.parity i)).hom.total N := rfl
  rw [← hraw, ← he] at h
  simpa only [coordinatePreDotPower, pow_one, preDotEnd_eq, Iso.conj_apply,
    Iso.symm_inv, Iso.symm_hom] using hc h

/-- Squaring removes the comparison sign, so the prescribed signed probe
polynomial holds on the actual shifted pre-induction dot. -/
theorem shiftedPreDot_odd_polynomial (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 1)
    (H : modulePiCategory D Sc m ⟶ R) :
    (shiftedPreDot D Sc m R i H ^ 2 + 1) ^ m i = 0 := by
  rw [shiftedPreDot_coordinates]
  exact signed_polynomial _ _ _ _ (coordinatePreDot_odd_polynomial D Sc m R i hi H)

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
