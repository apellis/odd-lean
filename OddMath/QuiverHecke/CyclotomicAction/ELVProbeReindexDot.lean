import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToDotUnit

/-! # The chosen OLD probe dot under representative changes

Brundan–Ellis (1.8), (1.12)–(1.14): the canonical append adjunction
comparison retains the specified signed dot on balanced tensors, including
the twist of arbitrary inhomogeneous quotient arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u

private theorem transform_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {J : C ⥤ A} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (N : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hα N).total w = transformLinear hα N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction Q).map f).total w = f.total (Q.obj w) := rfl
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν μ : List I} (h : ν.Perm μ) (i : I)
  {ν' μ' : List I} (hν : (i :: ν).Perm ν') (hμ : (i :: μ).Perm μ') (h' : ν'.Perm μ')
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν i ν' hν
local notation "K" => oldContentAppendTo D Sc cut μ i μ' hμ
local notation "R'" => oldContentReindex D Sc cut h'.symm
local notation "hDotν" => probeAppendToDot_supernatural D Sc m ν i ν' hν
local notation "hDotμ" => probeAppendToDot_supernatural D Sc m μ i μ' hμ

/-- The comparison intertwines the chosen physical signed dot on every vector. -/
theorem oldAppendReindexLinear_dot
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
    (w : OldContentCategory D Sc cut μ') :
    oldAppendReindexLinear D Sc cut h i hν hμ h' N w ∘ₗ
        transformLinear hDotν N ((R').obj w) =
      transformLinear hDotμ ((oldModuleReindex D Sc cut h).obj N) w ∘ₗ
        oldAppendReindexLinear D Sc cut h i hν hμ h' N w := by
  apply hom_ext J N.toFunctor (w := (R').obj w)
  intro s g b
  simp only [LinearMap.comp_apply]
  rw [transformLinear_tensor hDotν N ((R').obj w) s g b,
    oldAppendReindexIso_hom_tensor D Sc cut h i hν hμ h' N s w,
    oldAppendReindexIso_hom_tensor D Sc cut h i hν hμ h' N s w,
    transformLinear_tensor hDotμ ((oldModuleReindex D Sc cut h).obj N) w
      ((oldContentReindex D Sc cut h).obj s) g b]
  rfl

/-- The full supernatural module dot commutes with the even append comparison. -/
theorem oldAppendReindexIso_dot
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k)) :
    (restriction R').map (transformComponent hDotν N) ≫
        (oldAppendReindexIso D Sc cut h i hν hμ h').hom.app N =
      (oldAppendReindexIso D Sc cut h i hν hμ h').hom.app N ≫
        transformComponent hDotμ ((oldModuleReindex D Sc cut h).obj N) := by
  let V := (induction J ⋙ oldModuleReindex D Sc cut h').obj N
  let W := (oldModuleReindex D Sc cut h ⋙ induction K).obj N
  apply HomogeneousSuperfunctorIso.total_ext (F := V) (G := W)
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    restriction_total R' (transformComponent hDotν N) w,
    transform_total hDotν N ((R').obj w),
    transform_total hDotμ ((oldModuleReindex D Sc cut h).obj N) w]
  exact oldAppendReindexLinear_dot D Sc m h i hν hμ h' N w

end OddMath.QuiverHecke
