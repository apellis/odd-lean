import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightUnitCoordinates

/-! # Probe weight cap rows in their stored predecessor coordinates

Brundan–Ellis (1.13): preserve the chosen lower dot powers and counit
through the supported source equality at each stored successor block.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
private theorem rouquierPower_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {F : A ⟶ B} (d : F ⟶ F) (n : ℕ) (M : A.carrier) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]

private theorem left_whisker_total
    {k : Type u} [CommRing k] {A B E : PiSCat.{u,u,u + 1} k}
    (F : A ⟶ B) {G H : B ⟶ E} (z : G ⟶ H) (M : A.carrier) :
    (F ◁ z).total M = z.total (F.obj M) := rfl

private theorem cap_power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {E : A ⟶ B} {F : B ⟶ A} (a : SKM.SuperAdjunction (k := k) E F)
    (d : End E) (n : ℕ) (M : B.carrier) :
    (F ◁ SKM.rouquierPower d n ≫ a.counit).total M =
      ((show End (E.obj (F.obj M)) from d.total (F.obj M)) ^ n) ≫ a.counit.app 0 M := by
  rw [Superfunctor.comp_total, left_whisker_total, rouquierPower_total,
    HomogeneousSuperfunctorIso.total_eq_app a.counit a.counit_mem]

private theorem conjugate_power_counit
    {A : Type*} [Category A] [Preadditive A]
    {V W Z : A} (h : W = V) (d : End V) (ε : V ⟶ Z) (n : ℕ) :
    ((show End W from eqToHom h ≫ d ≫ eqToHom h.symm) ^ n) ≫
      (eqToHom h ≫ ε) = eqToHom h ≫ (d ^ n) ≫ ε := by
  subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (β : WeightBlocks D Λ x)
local notation "δ" => blockSucc D Λ i h β
local notation "Res" => probeOldBlockRes D Sc m i Λ h β
local notation "A" => probeOldActionAdjunction D Sc m i Λ h
local notation "d" => probeOldActionDot D Sc m i Λ h
local notation "F" => probeOldF D Sc m i Λ h
local notation "perm" => probeOldBlockTarget_perm D i Λ h β (blockSucc D Λ i h β) rfl

private theorem counit_dotPower_comparison
    (M : ProbeOldWeightProduct D Sc m Λ y) (n : ℕ) :
    ((show End ((probeOldInductionComponent D Sc m i Λ h δ).obj ((F).obj M)) from
      probeOldWeightDotComponent D Sc m i Λ h (D.parity i) ((F).obj M) δ) ^ n) ≫
      (probeOldWeightCounit D Sc m i Λ h).app M δ =
    eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M)) ≫
      ((show End ((probeOldBlockInd D Sc m i Λ h β).obj ((Res).obj (M δ))) from
        (probeOldBlockDot D Sc m i Λ h β).app (D.parity i) ((Res).obj (M δ))) ^ n) ≫
      (probeOldBlockAdj D Sc m i Λ h β).counit.app (M δ) := by
  dsimp only [probeOldWeightCounit]
  rw [probeOldWeightDotComponent_blockSucc, probeOldWeightCounitComponent_blockSucc]
  exact conjugate_power_counit
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M))
    ((probeOldBlockDot D Sc m i Λ h β).app (D.parity i) ((Res).obj (M δ)))
    ((probeOldBlockAdj D Sc m i Λ h β).counit.app (M δ)) n

private theorem storedCapRow_total (N : ProbeCanonicalModules D Sc m δ.1) (n : ℕ) :
    (probeAppendToCapRow D Sc m β.1.toList i perm n).total N =
      ((show End ((probeOldBlockInd D Sc m i Λ h β).obj ((Res).obj N)) from
        (probeOldBlockDot D Sc m i Λ h β).app (D.parity i) ((Res).obj N)) ^ n) ≫
        (probeOldBlockAdj D Sc m i Λ h β).counit.app N := by
  have ht := cap_power_total
    (probeAppendToRightAdjunction D Sc m β.1.toList i δ.1.toList perm)
    (probeAppendToInductionDot D Sc m β.1.toList i δ.1.toList perm) n N
  have hd := HomogeneousSuperfunctorIso.total_eq_app
    (probeOldBlockDot D Sc m i Λ h β) (probeOldBlockDot_mem D Sc m i Λ h β) ((Res).obj N)
  dsimp only [probeAppendToCapRow, probeAppendToDotPower] at ht ⊢
  rw [hd] at ht
  exact ht

/-- Every supported chosen global power/cap row retains the whole stored row. -/
theorem probeOldWeightCapPower_total_comparison
    (M : ProbeOldWeightProduct D Sc m Λ y) (n : ℕ) :
    ((F ◁ SKM.rouquierPower d n) ≫ (A).counit).total M δ =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M)) ≫
        (probeAppendToCapRow D Sc m β.1.toList i perm n).total (M δ) := by
  have ht := Superfunctor.comp_total (F ◁ SKM.rouquierPower d n) (A).counit M
  rw [left_whisker_total] at ht
  have hc : (A).counit.total M = (probeOldWeightCounit D Sc m i Λ h).app M := by
    change (probeOldWeightCounit D Sc m i Λ h).app M + 0 = _
    exact add_zero _
  rw [hc] at ht
  have ha := congrFun ht δ
  simp only [Pi.comp_apply] at ha
  rw [probeOldWeightDotPower_total_component] at ha
  have hr := congrArg (fun f :
      (probeOldBlockInd D Sc m i Λ h β).obj ((Res).obj (M δ)) ⟶ M δ =>
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β ((F).obj M)) ≫ f)
    (storedCapRow_total D Sc m i Λ h β (M δ) n).symm
  exact ha.trans ((counit_dotPower_comparison D Sc m i Λ h β M n).trans hr)

end OddMath.QuiverHecke
