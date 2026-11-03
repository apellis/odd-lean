import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitTensors

/-! # Balanced tensors under OLD representative changes

The canonical append comparison used for Brundan–Ellis (1.12)–(1.14)
preserves the literal unit tensors. Its tensor formula identifies the chosen
append operators at arbitrary content representatives.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u

private theorem restriction_comparison_total
    {k C A B : Type u} [CommRing k] [Category.{u} C] [Category.{u} A] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (Q : A ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M : Superfunctor k C (SVec k)} {N P : Superfunctor k B (SVec k)}
    (a : M ⟶ (restriction Q ⋙ restriction J).obj N) (b : N ⟶ P) (v : C) (x : M.obj v) :
    (a ≫ (restriction Q ⋙ restriction J).map b).total v x =
      b.total (Q.obj (J.obj v)) (a.total v x) := by
  rw [Superfunctor.comp_total]
  rfl

private theorem unit_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) (v : C) (x : M.obj v) :
    ((adjunction J).unit.app M).total v x = unit J M.toFunctor v x := by
  change (unit J M.toFunctor v + 0) x = _
  rw [add_zero]

private theorem restriction_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {N P : Superfunctor k A (SVec k)} (b : N ⟶ P) (v : C) (x : N.obj (Q.obj v)) :
    ((restriction Q).map b).total v x = b.total (Q.obj v) x := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  {ν μ : List I} (h : ν.Perm μ) (i : I)
  {ν' μ' : List I} (hν : (i :: ν).Perm ν') (hμ : (i :: μ).Perm μ') (h' : ν'.Perm μ')
local notation "J" => oldContentAppendTo D Sc cutoff ν i ν' hν
local notation "K" => oldContentAppendTo D Sc cutoff μ i μ' hμ
local notation "Q" => oldContentReindex D Sc cutoff h
local notation "Q'" => oldContentReindex D Sc cutoff h'
local notation "E" => oldAppendReindexIso D Sc cutoff h i hν hμ h'

theorem oldAppendReindexLeftAdjunction_unit
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldAppendReindexLeftAdjunction D Sc cutoff i hν h').unit.app N =
      (adjunction J).unit.app N := by
  rw [oldAppendReindexLeftAdjunction, Adjunction.comp_unit_app]
  change (adjunction J).unit.app N ≫ (restriction J).map (𝟙 _) = _
  rw [(restriction J).map_id]
  exact Category.comp_id _

theorem oldAppendReindexRightAdjunction_unit
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldAppendReindexRightAdjunction D Sc cutoff h i hν hμ h').unit.app N =
      (restriction Q).map ((adjunction K).unit.app ((oldModuleReindex D Sc cutoff h).obj N)) := by
  rw [oldAppendReindexRightAdjunction, Adjunction.comp_unit_app]
  change 𝟙 _ ≫ (restriction Q).map _ = _
  rw [Category.id_comp]

/-- The adjunction comparison sends the chosen unit to the chosen unit. -/
theorem oldAppendReindexIso_hom_unit
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (b : N.obj s) :
    ((E).hom.app N).total ((Q').obj ((J).obj s)) (unit J N.toFunctor s b) =
      unit K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) b := by
  have he := oldAppendReindexIso_unit D Sc cutoff h i hν hμ h' N
  rw [oldAppendReindexLeftAdjunction_unit, oldAppendReindexRightAdjunction_unit] at he
  have hv := congrArg (fun f => f.total s b) he
  rw [restriction_comparison_total J Q' ((adjunction J).unit.app N) ((E).hom.app N) s b,
    unit_total_apply J N s b,
    restriction_total_apply Q ((adjunction K).unit.app ((oldModuleReindex D Sc cutoff h).obj N)) s b,
    unit_total_apply K ((oldModuleReindex D Sc cutoff h).obj N) ((Q).obj s) b] at hv
  exact hv

end OddMath.QuiverHecke
