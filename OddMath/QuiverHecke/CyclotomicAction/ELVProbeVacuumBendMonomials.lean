import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightNegativeCap
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirPostUnitStandard
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMatrixNaturality

/-! # Vacuum coordinates of the ordered mixed-bend monomials

SwappedHomInversion §3 (4)–(5): compare the prescribed negative pre-cap
and dotted post-unit before summing the finite padded Dx expansion.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction
universe u
local instance bendMonomialHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

private def totalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem unitColumn_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N 0) (r : ℕ) :
    unitDotColumn J hα M r ≫ (restriction J).map ((induction J).map f) =
      f ≫ unitDotColumn J hα N r := by
  have h := (unitDotColumn_supernatural J hα r).naturality hf
  simpa only [mul_zero, sign_zero, one_smul] using h.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I) {muP nuR : X} (edgeP : -ΛP + D.α i = -muP)
  (edgeR : -ΛR + D.α i = nuR) (β : I →₀ ℕ)
local notation "T" => probeOldRouquierFamily D Sc m ΛP hcP
local notation "W" => elvRouquierFamily D Sc cutoff bound ΛR hcR
local notation "N₀" => regularProbe D Sc m ΛP
local notation "δ" => emptyBlock D ΛR
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "J" => contentAppend D Sc cutoff bound (0 : Multiset I) [i]
local notation "hd" => canonicalAppendDot_supernatural D Sc cutoff bound (0 : Multiset I) i
variable (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ (W).obj (-ΛR))

/-- The output block functor retains the entire probe module. -/
def vacuumBendBlock : ProbeVacuumCap.modulePiCategory D Sc m ⟶ R₀ :=
  H ≫ elvBlockEval D Sc cutoff bound ΛR δ
local notation "H₀" => OddMath.QuiverHecke.ELVOld.WeightTensorVacuum.vacuumBendBlock D Sc m cutoff bound ΛR hcR H
local notation "Z" => preCapInput D Sc m ΛP hcP (elvRouquierFamily D Sc cutoff bound ΛR hcR).obj (-ΛR) H
local notation "Q" => SKM.homContentPostF (probeOldRouquierFamily D Sc m ΛP hcP).obj W i β ΛP edgeR
local notation "E" => SKM.homContentPostE (probeOldRouquierFamily D Sc m ΛP hcP).obj W i β ΛP edgeR

/-- The prescribed post-target comparison, stored successor-content
chart, and regular-input comparison, in chronological order. -/
def vacuumBendPostTargetIso :
    (((Q).obj ((E).obj Z)).obj N₀) δ ≅
      (restriction J).obj ((induction J).obj ((H₀).obj (probeOldVacuumRegular D Sc m))) :=
  (totalEvaluation N₀ ⋙ Pi.eval _ δ).mapIso
      (SKM.homContentPostTargetIso (T).obj W i β ΛP edgeR Z) ≪≫
    eqToIso (elvWeightFollowing_obj D Sc cutoff bound i ΛR edgeR δ ((Z).obj N₀)) ≪≫
    eqToIso (storedAppendUpper_obj D Sc cutoff bound δ.1 i
      (blockSucc D ΛR i edgeR δ).1 (elvBlockSucc_content_eq D i ΛR edgeR δ) (((Z).obj N₀) δ)) ≪≫
    (induction J ⋙ restriction J).mapIso
      ((H₀).toFunctor.mapIso (eqToIso (emptyProbe_regular D Sc m ΛP)))

/-- At the empty reservoir block, the actual shifted post-cup becomes
the raw native unit/dot column, with the regular-input cast retained. -/
theorem vacuumBendPostCup_native (r : ℕ) :
    ((SKM.homContentPostCup (T).obj W i β ΛP edgeR r Z).total N₀) δ ≫
      (vacuumBendPostTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (H₀).map (eqToHom (emptyProbe_regular D Sc m ΛP)) ≫
      unitDotColumn J hd ((H₀).obj (probeOldVacuumRegular D Sc m)) r := by
  have hp := reservoirPostCup_canonical D Sc cutoff bound ΛR hcR (T).obj i β ΛP edgeR r Z N₀ δ
  have hn := unitColumn_even J hd ((H₀).map (eqToHom (emptyProbe_regular D Sc m ΛP)))
    (Supercategory.map_mem H₀ (eqToHom_mem_parity_zero (k := k) (emptyProbe_regular D Sc m ΛP))) r
  rw [unitDotColumn_eq_restrictedDotEnd] at hn
  have ht := congrArg (fun f => f ≫
    (restriction J).map ((induction J).map
      ((H₀).map (eqToHom (emptyProbe_regular D Sc m ΛP))))) hp
  change _ = _ at ht
  simpa only [vacuumBendPostTargetIso, Iso.trans_hom, Functor.mapIso_hom,
    eqToIso.hom, Functor.comp_map, Category.assoc] using ht.trans hn

local instance bendMonomialProbeDotIso : IsIso ((T).dot i edgeP) :=
  (isUnit_iff_isIso _).mp (probeOldRouquierFamily_dot_isUnit D Sc m ΛP hcP i edgeP)

/-- Each prescribed negative pre-cap followed by a dotted post-unit is
the corresponding raw vacuum bend monomial, with no compatibility premise. -/
theorem vacuumBendMonomial_native (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1)
    (n r : ℕ) :
    ((SKM.homPreNegativeCap T (W).obj i (-ΛR) edgeP n Z ≫
      SKM.homContentPostCup (T).obj W i β ΛP edgeR r Z).total N₀) δ ≫
      (vacuumBendPostTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreSourceIso D Sc m ΛP hcP (fun _ => R₀) (-ΛR) i edgeP H₀).hom ≫
      (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m R₀ i H₀) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D Sc m R₀ i hP H₀ ≫
          (adjunction J).unit.app ((H₀).obj (probeOldVacuumRegular D Sc m)) ≫
            restrictedDotEnd J hd ((H₀).obj (probeOldVacuumRegular D Sc m)) ^ r := by
  have hp := vacuumBendPostCup_native D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H r
  have hn := vacuumPreNegativeCap_native D Sc m ΛP hcP (fun _ => R₀) (-ΛR) i edgeP H₀ hP hi n
  have hc : ((SKM.homPreNegativeCap T (W).obj i (-ΛR) edgeP n Z).total N₀) δ ≫
      (H₀).map (eqToHom (emptyProbe_regular D Sc m ΛP)) =
      (vacuumPreSourceIso D Sc m ΛP hcP (fun _ => R₀) (-ΛR) i edgeP H₀).hom ≫
        (Ring.inverse (ProbeVacuumCap.shiftedPreDot D Sc m R₀ i H₀) ^ n) ≫
          ProbeVacuumCap.shiftedPreCap D Sc m R₀ i hP H₀ := by
    convert hn using 1 <;> rfl
  rw [Superfunctor.comp_total]
  change (((SKM.homPreNegativeCap T (W).obj i (-ΛR) edgeP n Z).total N₀) δ ≫
    ((SKM.homContentPostCup (T).obj W i β ΛP edgeR r Z).total N₀) δ) ≫ _ = _
  rw [Category.assoc, hp, ← Category.assoc, hc, unitDotColumn_eq_restrictedDotEnd]
  simp only [Category.assoc]

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
