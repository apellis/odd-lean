import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDot
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToRows

/-! # Probe weight unit columns in their stored successor coordinates

Brundan–Ellis (1.14): retain the selected upper unit and every ordered
power of the selected dot on every output block, including blocks with
no lower predecessor. These are the columns of the stored local inverse.
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

private theorem right_whisker_total
    {k : Type u} [CommRing k] {A B E : PiSCat.{u,u,u + 1} k}
    {F G : A ⟶ B} (z : F ⟶ G) (R : B ⟶ E) (M : A.carrier) :
    (z ▷ R).total M = R.map (z.total M) := by
  change R.toFunctor.map (z.app 0 M) + R.toFunctor.map (z.app 1 M) =
    R.toFunctor.map (z.app 0 M + z.app 1 M)
  exact (CategoryTheory.Functor.map_add R.toFunctor).symm

private theorem product_end_power
    {ι : Type*} {V : ι → Type*} [∀ a, Category (V a)]
    {M : ∀ a, V a} (d : End M) (n : ℕ) (a : ι) :
    (d ^ n) a = (show End (M a) from d a) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', End.mul_def, Pi.comp_apply, ih]

private theorem unit_conjugate_power
    {A B : Type*} [Category A] [Preadditive A] [Category B]
    (R : A ⥤ B) {P : B} {W V : A} (h : W = V)
    (η : P ⟶ R.obj V) (d : End V) (n : ℕ) :
    ((η ≫ R.map (eqToHom h.symm)) ≫
        R.map ((show End W from eqToHom h ≫ d ≫ eqToHom h.symm) ^ n)) ≫
      R.map (eqToHom h) = η ≫ R.map (d ^ n) := by
  subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]

private theorem unit_power_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {E : A ⟶ B} {F : B ⟶ A} (a : SKM.SuperAdjunction (k := k) E F)
    (d : End E) (n : ℕ) (M : A.carrier) :
    (a.unit ≫ SKM.rouquierPower d n ▷ F).total M =
      a.unit.app 0 M ≫ F.map ((show End (E.obj M) from d.total M) ^ n) := by
  rw [Superfunctor.comp_total, right_whisker_total, rouquierPower_total,
    HomogeneousSuperfunctorIso.total_eq_app a.unit a.unit_mem]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (δ : WeightBlocks D Λ x)
local notation "ε" => blockSucc D Λ i h δ
local notation "Res" => probeOldBlockRes D Sc m i Λ h δ
local notation "A" => probeOldActionAdjunction D Sc m i Λ h
local notation "d" => probeOldActionDot D Sc m i Λ h
local notation "F" => probeOldF D Sc m i Λ h
local notation "perm" => probeOldBlockTarget_perm D i Λ h δ (blockSucc D Λ i h δ) rfl

/-- The selected ordered dot powers retain their literal component powers. -/
theorem probeOldWeightDotPower_total_component
    (M : ProbeOldWeightProduct D Sc m Λ x) (n : ℕ) (ζ : WeightBlocks D Λ y) :
    (SKM.rouquierPower d n).total M ζ =
      (show End ((probeOldInductionComponent D Sc m i Λ h ζ).obj M) from
        probeOldWeightDotComponent D Sc m i Λ h (D.parity i) M ζ) ^ n := by
  have hP := rouquierPower_total d n M
  have hD := HomogeneousSuperfunctorIso.total_eq_app d (probeOldActionDot_mem D Sc m i Λ h) M
  have he := congrFun hP ζ
  rw [product_end_power, hD] at he
  exact he

private theorem unit_dotPower_comparison
    (M : ProbeOldWeightProduct D Sc m Λ x) (n : ℕ) :
    ((probeOldWeightUnitApp D Sc m i Λ h δ M ≫
        (Res).map ((show End ((probeOldInductionComponent D Sc m i Λ h ε).obj M) from
          probeOldWeightDotComponent D Sc m i Λ h (D.parity i) M ε) ^ n)) ≫
      (Res).map (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M))) =
    (probeOldBlockAdj D Sc m i Λ h δ).unit.app (M δ) ≫
      (Res).map ((show End ((probeOldBlockInd D Sc m i Λ h δ).obj (M δ)) from
        (probeOldBlockDot D Sc m i Λ h δ).app (D.parity i) (M δ)) ^ n) := by
  rw [probeOldWeightDotComponent_blockSucc]
  exact unit_conjugate_power (Res).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M)
    ((probeOldBlockAdj D Sc m i Λ h δ).unit.app (M δ))
    ((probeOldBlockDot D Sc m i Λ h δ).app (D.parity i) (M δ)) n

private theorem storedUnitColumn_total (N : ProbeCanonicalModules D Sc m δ.1) (n : ℕ) :
    (probeAppendToUnitColumn D Sc m δ.1.toList i perm n).total N =
      (probeOldBlockAdj D Sc m i Λ h δ).unit.app N ≫
        (Res).map ((show End ((probeOldBlockInd D Sc m i Λ h δ).obj N) from
          (probeOldBlockDot D Sc m i Λ h δ).app (D.parity i) N) ^ n) := by
  have ht := unit_power_total
    (probeAppendToRightAdjunction D Sc m δ.1.toList i ε.1.toList perm)
    (probeAppendToInductionDot D Sc m δ.1.toList i ε.1.toList perm) n N
  have hd := HomogeneousSuperfunctorIso.total_eq_app
    (probeOldBlockDot D Sc m i Λ h δ) (probeOldBlockDot_mem D Sc m i Λ h δ) N
  dsimp only [probeAppendToUnitColumn, probeAppendToDotPower] at ht ⊢
  rw [hd] at ht
  exact ht

/-- Every chosen global unit/power column retains its entire stored-target column. -/
theorem probeOldWeightUnitPower_total_comparison
    (M : ProbeOldWeightProduct D Sc m Λ x) (n : ℕ) :
    ((A).unit ≫ SKM.rouquierPower d n ▷ F).total M δ ≫
      (Res).map (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M)) =
    (probeAppendToUnitColumn D Sc m δ.1.toList i perm n).total (M δ) := by
  have ht := unit_power_total A d n M
  have hu : (A).unit.app 0 M = (probeOldWeightUnit D Sc m i Λ h).app M := rfl
  rw [hu] at ht
  have ha := congrFun ht δ
  dsimp only [probeOldF, Superfunctor.map, productFunctor, Functor.pi'] at ha
  simp only [Pi.comp_apply] at ha
  rw [product_end_power] at ha
  have hd := HomogeneousSuperfunctorIso.total_eq_app d (probeOldActionDot_mem D Sc m i Λ h) M
  have hδ := congrFun hd ε
  rw [hδ] at ha
  have hc := congrArg (fun f => f ≫ (Res).map
    (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h δ M))) ha
  exact hc.trans ((unit_dotPower_comparison D Sc m i Λ h δ M n).trans
    (storedUnitColumn_total D Sc m i Λ h δ (M δ) n).symm)

end OddMath.QuiverHecke
