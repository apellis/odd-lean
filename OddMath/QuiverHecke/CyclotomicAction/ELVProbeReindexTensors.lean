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

private theorem even_map_naturality
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (e : M ⟶ N)
    (he : e ∈ parity (R := k) _ _ 0) {v w : C} (g : v ⟶ w) (b : M.obj v) :
    e.total w (M.map g b) = N.map g (e.total v b) := by
  rw [HomogeneousSuperfunctorIso.total_eq_app e he w,
    HomogeneousSuperfunctorIso.total_eq_app e he v]
  exact congrArg (fun f : M.obj v ⟶ N.obj w => f b) (e.toNatTrans.naturality g)

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
  let V := (induction J ⋙ oldModuleReindex D Sc cutoff h').obj N
  let W := (oldModuleReindex D Sc cutoff h ⋙ induction K).obj N
  let e : V ⟶ W := (E).hom.app N
  let a : N ⟶ (restriction Q' ⋙ restriction J).obj V := (adjunction J).unit.app N
  let r : N ⟶ (restriction Q' ⋙ restriction J).obj W :=
    (restriction Q).map ((adjunction K).unit.app ((oldModuleReindex D Sc cutoff h).obj N))
  have he' : a ≫ (restriction Q' ⋙ restriction J).map e = r := he
  have hv := congrArg (fun f : N ⟶ (restriction Q' ⋙ restriction J).obj W => f.total s b) he'
  have hc := restriction_comparison_total J Q' a e s b
  have hu := unit_total_apply J N s b
  have hr := restriction_total_apply Q
    ((adjunction K).unit.app ((oldModuleReindex D Sc cutoff h).obj N)) s b
  have hv' := unit_total_apply K ((oldModuleReindex D Sc cutoff h).obj N) ((Q).obj s) b
  have ht : e.total ((Q').obj ((J).obj s)) (a.total s b) = r.total s b := hc.symm.trans hv
  have hul : a.total s b = unit J N.toFunctor s b := hu
  have hur : r.total s b =
      unit K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) b := hr.trans hv'
  exact (congrArg (e.total ((Q').obj ((J).obj s))) hul).symm.trans (ht.trans hur)

/-- The forward comparison in its two fixed balanced coend carriers. -/
def oldAppendReindexLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldContentCategory D Sc cutoff μ') :
    Obj J N.toFunctor ((oldContentReindex D Sc cutoff h'.symm).obj w) →ₗ[k]
      Obj K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor w :=
  ((E).hom.app N).total w

/-- The comparison only changes the source permutation certificate of a tensor. -/
theorem oldAppendReindexIso_hom_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν) (w : OldContentCategory D Sc cutoff μ')
    (g : (J).obj s ⟶ (oldContentReindex D Sc cutoff h'.symm).obj w) (b : N.obj s) :
    oldAppendReindexLinear D Sc cutoff h i hν hμ h' N w (tensor J N.toFunctor s g b) =
      tensor K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) g b := by
  let V := (induction J ⋙ oldModuleReindex D Sc cutoff h').obj N
  let W := (oldModuleReindex D Sc cutoff h ⋙ induction K).obj N
  let e : V ⟶ W := (E).hom.app N
  let a : (Q').obj ((J).obj s) ⟶ w := g
  have hn := even_map_naturality e (oldAppendReindexIso_hom_mem D Sc cutoff h i hν hμ h' N)
    a (unit J N.toFunctor s b)
  have hL : V.map a (unit J N.toFunctor s b) = tensor J N.toFunctor s g b :=
    postcompose_unit J N.toFunctor (v := s)
      (w := (oldContentReindex D Sc cutoff h'.symm).obj w) g b
  have hu := oldAppendReindexIso_hom_unit D Sc cutoff h i hν hμ h' N s b
  have hr := congrArg (W.map a) hu
  have hR : W.map a (unit K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) b) =
      tensor K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor ((Q).obj s) g b :=
    postcompose_unit K ((oldModuleReindex D Sc cutoff h).obj N).toFunctor
      (v := (Q).obj s) (w := w) g b
  exact (congrArg (e.total w) hL).symm.trans (hn.trans (hr.trans hR))

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν μ : List I} (h : ν.Perm μ) (i : I)
  {ν' μ' : List I} (hν : (i :: ν).Perm ν') (hμ : (i :: μ).Perm μ') (h' : ν'.Perm μ')

end OddMath.QuiverHecke
