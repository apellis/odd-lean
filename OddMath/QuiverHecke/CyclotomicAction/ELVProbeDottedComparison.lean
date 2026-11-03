import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMateComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVOperatorPowerComparison

/-! # Given signed dot powers under mapped scalar append comparison

The dotted unit and cap entries in DeformedMatrixComparison (1), (2), (5)
use powers of the same signed dot. An independent intermediate module keeps
the selected append and restriction comparisons on their literal coends.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

private def appendDotCoefficient
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    (s : C) (t : A) (g : J.obj s ⟶ t) : J.obj s ⟶ t := α s ≫ twist k p g

private theorem dottedCoendHom_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A} {f g : Obj J M w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : M.obj s), f (tensor J M s a b) = g (tensor J M s a b)) :
    f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

private theorem dottedCoendComp_ext
    {k C A V W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    (f : Obj J M w →ₗ[k] V) (g : V →ₗ[k] Z)
    (h : Obj J M w →ₗ[k] W) (l : W →ₗ[k] Z)
    (hh : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      g (f (tensor J M s a b)) = l (h (tensor J M s a b))) : g ∘ₗ f = l ∘ₗ h := by
  apply dottedCoendHom_ext J M
  exact hh

private theorem dottedTensorSource_congr
    {k A B : Type u} [CommRing k] [Category.{u} A] [Category.{u} B]
    [Preadditive B] [Linear k B] (K : A ⥤ B) (M : A ⥤ SVec k)
    (w : B) (v v' : A) (e : v = v') (g : K.obj v ⟶ w) (g' : K.obj v' ⟶ w)
    (b : M.obj v) (b' : M.obj v') (hg : HEq g g') (hb : HEq b b') :
    tensor K M v g b = tensor K M v' g' b' := by
  cases e
  cases hg
  cases hb
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (R : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hR : ProbeEvaluatesCoefficients D m Sc ν R)
  (M : Superfunctor k (OrdinaryContentCategory D Sc
    (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))
  (c : probeOrdinaryModuleSuperfunctor D Sc m ν R hR ≅ M)
  (i : I) (hc : c.hom ∈ parity (R := k) _ _ 0)
include hc
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- The mapped selected append comparison intertwines the given signed dot.
Evenness is an intermediate premise, discharged by the canonical restriction
identity in the actual dotted-cap application. -/
theorem probeMappedAppendLinear_dot
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    probeMappedAppendLinear D Sc m ν R hR M c i w ∘ₗ
        probeOldContentInductionDot D Sc m ν i R w =
      transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) M ((U).obj w) ∘ₗ
        probeMappedAppendLinear D Sc m ν R hR M c i w := by
  apply dottedCoendComp_ext J R.toFunctor
  intro s g b
  have ho := probeOldContentInductionDot_tensor D Sc m ν i R s w g b
  have hq := probeMappedAppendLinear_tensor D Sc m ν R hR M c i hc s w
    (probeOldContentAppendDot D Sc m ν i s ≫ twist k (D.parity i) g) b
  have hl := (congrArg (probeMappedAppendLinear D Sc m ν R hR M c i w) ho).trans hq
  have hs := probeMappedAppendLinear_tensor D Sc m ν R hR M c i hc s w g b
  have ht := transformLinear_tensor (probeOrdinaryAppendDot_supernatural D Sc m ν i) M
    ((U).obj w) ((Q).obj s) ((U).map g) (c.hom.total ((Q).obj s) b)
  have hr := (congrArg (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i)
    M ((U).obj w)) hs).trans ht
  let aNew := appendDotCoefficient (k := k) T (p := D.parity i)
    (α := probeOrdinaryAppendDot D Sc m ν i) ((Q).obj s) ((U).obj w) ((U).map g)
  have ha : HEq ((U).map (probeOldContentAppendDot D Sc m ν i s ≫
      twist k (D.parity i) g)) aNew := by
    apply heq_of_eq
    dsimp only [aNew, appendDotCoefficient, probeOldContentAppendDot]
    rw [(U).map_comp, map_twist, probeOrdinaryAppendDot_old D Sc m ν i s]
    rfl
  have he := dottedTensorSource_congr T M.toFunctor ((U).obj w) ((Q).obj s) ((Q).obj s)
    rfl _ aNew (c.hom.total ((Q).obj s) b) (c.hom.total ((Q).obj s) b) ha HEq.rfl
  have hmid := he.trans hr.symm
  have hfinal := hl.trans hmid
  exact hfinal

/-- Every power of the given signed dot is transported by the same comparison;
no triangular change of dotted generators or additional parity premise is used. -/
theorem probeMappedAppendLinear_dot_pow
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (n : ℕ) :
    probeMappedAppendLinear D Sc m ν R hR M c i w ∘ₗ
        ((probeOldContentInductionDot D Sc m ν i R w) ^ n) =
      ((transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) M ((U).obj w)) ^ n) ∘ₗ
        probeMappedAppendLinear D Sc m ν R hR M c i w :=
  intertwine_pow (probeMappedAppendLinear D Sc m ν R hR M c i w)
    (probeOldContentInductionDot D Sc m ν i R w)
    (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) M ((U).obj w))
    (probeMappedAppendLinear_dot D Sc m ν R hR M c i hc w) n

end OddMath.QuiverHecke
