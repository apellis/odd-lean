import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDoubleAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionDoubleTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRestrictionComparison

/-! # The chosen ordinary-adjunction crossing mate under scalar specialization

The first crossing-derived matrix entry in DeformedMatrixComparison (2), (4)
uses the ordered ordinary-adjunction mate. The scalar comparison must keep
the chosen append isomorphisms, literal restriction equality, unit and
unshifted counit. Normalized cap rows remain separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

section GenericMaps
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

private theorem probeMateEqToHom_mem {R M : Superfunctor k C (SVec k)} (h : R = M) :
    (eqToHom h : R ⟶ M) ∈ parity (R := k) _ _ 0 := by
  subst M
  exact id_mem R


variable {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α) (M : Superfunctor k A (SVec k))

omit [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K] in
private def probeGridMateCoefficient (t : A) (v : B) (e : K.obj t = v)
    (s : C) (g : J.obj s ⟶ t) : (J ⋙ K).obj s ⟶ v :=
  (α s ≫ twist k p (K.map g)) ≫ eqToHom e

omit [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K] in
private def probeGridSignedMateCoefficient (t : A) (v : B) (e : K.obj t = v)
    (s : C) (g : J.obj s ⟶ t) : (J ⋙ K).obj s ⟶ v :=
  -probeGridMateCoefficient (k := k) J K (p := p) (α := α) t v e s g

/-- The given ordered changing-content mate followed by its prescribed output-object transport. -/
def endpointGridMateLinear (t : A) (v : B) (e : K.obj t = v) :
    Obj J ((restriction J).obj M).toFunctor t →ₗ[k] Obj K M.toFunctor v :=
  postcompose K M.toFunctor (eqToHom e) ∘ₗ orderedGridMateLinear J K hα M t

private theorem endpointGridMateLinear_tensor (t : A) (v : B) (e : K.obj t = v)
    (s : C) (g : J.obj s ⟶ t) (b : M.obj (J.obj s)) :
    endpointGridMateLinear J K hα M t v e
      (tensor J ((restriction J).obj M).toFunctor s g b) =
    tensor K M.toFunctor (J.obj s)
      (probeGridSignedMateCoefficient (k := k) J K (p := p) (α := α) t v e s g) b := by
  dsimp only [endpointGridMateLinear, LinearMap.comp_apply]
  rw [orderedGridMateLinear_tensor, postcompose_tensor]
  unfold probeGridSignedMateCoefficient probeGridMateCoefficient
  rw [Preadditive.neg_comp]


end GenericMaps

private theorem probeCoendHom_ext
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

private theorem probeCoendComp_ext
    {k C A V W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    (f : Obj J M w →ₗ[k] V) (g : V →ₗ[k] Z)
    (h : Obj J M w →ₗ[k] W) (l : W →ₗ[k] Z)
    (hh : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      g (f (tensor J M s a b)) = l (h (tensor J M s a b))) : g ∘ₗ f = l ∘ₗ h := by
  apply probeCoendHom_ext J M
  exact hh

private theorem probeTensorSource_congr
    {k A B : Type u} [CommRing k] [Category.{u} A] [Category.{u} B]
    [Preadditive B] [Linear k B] (K : A ⥤ B) (M : A ⥤ SVec k)
    (w : B) (v v' : A) (e : v = v') (g : K.obj v ⟶ w) (g' : K.obj v' ⟶ w)
    (b : M.obj v) (b' : M.obj v') (hg : HEq g g') (hb : HEq b b') :
    tensor K M v g b = tensor K M v' g' b' := by
  cases e
  cases hg
  cases hb
  rfl

private theorem probeNegHom_heq {B : Type u} [Category.{u} B] [Preadditive B]
    {v w v' w' : B} (ev : v = v') (ew : w = w')
    {g : v ⟶ w} {g' : v' ⟶ w'} (h : HEq g g') : HEq (-g) (-g') := by
  cases ev
  cases ew
  cases h
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "K" => ELVOld.oldContentAppend D Sc cut (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "Q₀" => probeOldOrdinaryFunctor D Sc m ν
local notation "Q₁" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "Q₂" => probeOldOrdinaryFunctor D Sc m (i :: i :: ν)
variable (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN

/-- The chosen lower append comparison followed by induction of the literal
ordinary restriction equality, on the original old restricted module. -/
abbrev probeMateSourceComparisonLinear
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMappedAppendLinear D Sc m ν ((restriction J).obj N)
    (probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN)
    ((restriction T).obj O)
    (eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)) i t

/-- The source comparison retains every coefficient arrow and vector. -/
theorem probeMateSourceComparisonLinear_tensor
    (s : ELVOld.OldContentCategory D Sc cut ν)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (g : (J).obj s ⟶ t) (b : N.obj ((J).obj s)) :
    probeMappedAppendLinear D Sc m ν ((restriction J).obj N)
        (probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN)
        ((restriction T).obj O)
        (eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)) i t
      (tensor J (((restriction J).obj N)).toFunctor s g b) =
      tensor T ((restriction T).obj O).toFunctor ((Q₀).obj s) ((Q₁).map g) b := by
  have he : (eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)).hom ∈
      parity (R := k) _ _ 0 :=
      probeMateEqToHom_mem (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)
  have h := probeMappedAppendLinear_tensor D Sc m ν ((restriction J).obj N)
    (probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN)
    ((restriction T).obj O)
    (eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)) i he s t g b
  have hb : (eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)).hom.total
      ((Q₀).obj s) b = b := by
    rw [SuperNatTrans.total]
    change (eqToHom (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)).app 0
        ((Q₀).obj s) b +
      (eqToHom (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)).app 1
        ((Q₀).obj s) b = b
    rw [probeRestrictionEqToHom_app, probeRestrictionEqToHom_app]
    simp only [ite_true, one_ne_zero, ite_false]
    change b + 0 = b
    exact add_zero b
  have hright := congrArg
    (tensor T ((restriction T).obj O).toFunctor ((Q₀).obj s) ((Q₁).map g)) hb
  exact h.trans hright

/-- The selected append comparisons and literal restriction equality carry
the prescribed signed ordinary-adjunction mate to its ordinary scalar mate.
All old coend vectors are included; no mate formula is assumed. -/
theorem probeAppendOrdinaryModuleIso_mate
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    probeAppendComparisonLinear D Sc m (i :: ν) N hN i ((K).obj t) ∘ₗ
      orderedGridMateLinear J K (probeOldContentEqualCross_supernatural D Sc m ν i) N t =
    endpointGridMateLinear T S (probeOrdinaryEqualCross_supernatural D Sc m ν i) O
        ((Q₁).obj t) ((Q₂).obj ((K).obj t)) rfl ∘ₗ
      probeMappedAppendLinear D Sc m ν ((restriction J).obj N)
        (probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN)
        ((restriction T).obj O)
        (eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)) i t := by
  apply probeCoendComp_ext J ((restriction J).obj N).toFunctor
  intro s g b
  have ho := orderedGridMateLinear_tensor J K
    (probeOldContentEqualCross_supernatural D Sc m ν i) N s t g b
  have hq := probeAppendOrdinaryModuleIso_hom_tensor D Sc m (i :: ν) N hN i
    ((J).obj s) ((K).obj t)
    (-(probeOldContentEqualCross D Sc m ν i s ≫ twist k (D.parity i * D.parity i) ((K).map g))) b
  have hl := (congrArg (probeAppendComparisonLinear D Sc m (i :: ν) N hN i ((K).obj t)) ho).trans hq
  have hs := probeMateSourceComparisonLinear_tensor D Sc m ν i N hN s t g b
  have ht := endpointGridMateLinear_tensor T S
    (probeOrdinaryEqualCross_supernatural D Sc m ν i) O
    ((Q₁).obj t) ((Q₂).obj ((K).obj t)) rfl ((Q₀).obj s) ((Q₁).map g) b
  have hr := (congrArg (endpointGridMateLinear T S
    (probeOrdinaryEqualCross_supernatural D Sc m ν i) O
    ((Q₁).obj t) ((Q₂).obj ((K).obj t)) rfl) hs).trans ht
  let aNew := probeGridMateCoefficient (k := k) T S
    (p := D.parity i * D.parity i) (α := probeOrdinaryEqualCross D Sc m ν i)
    ((Q₁).obj t) ((Q₂).obj ((K).obj t)) rfl ((Q₀).obj s) ((Q₁).map g)
  have hmap := (eqToHom (probeOldOrdinaryFunctor_append D Sc m (i :: ν) i)).naturality g
  simp only [eqToHom_app, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.comp_map] at hmap
  have hu : HEq ((Q₂).map (probeOldContentEqualCross D Sc m ν i s ≫
      twist k (D.parity i * D.parity i) ((K).map g))) aNew := by
    apply heq_of_eq
    dsimp only [aNew, probeGridMateCoefficient]
    rw [(Q₂).map_comp, map_twist, probeOrdinaryEqualCross_old D Sc m ν i s, hmap]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  have ha := (heq_of_eq ((Q₂).map_neg (f :=
    (probeOldContentEqualCross D Sc m ν i s ≫ twist k (D.parity i * D.parity i) ((K).map g))))).trans
      (probeNegHom_heq (show (Q₂).obj ((K).obj ((J).obj s)) =
        (S).obj ((T).obj ((Q₀).obj s)) from rfl) rfl hu)
  have he := probeTensorSource_congr S (O).toFunctor ((Q₂).obj ((K).obj t))
    ((Q₁).obj ((J).obj s)) ((T).obj ((Q₀).obj s)) rfl _
    (probeGridSignedMateCoefficient (k := k) T S (p := D.parity i * D.parity i)
      (α := probeOrdinaryEqualCross D Sc m ν i)
      ((Q₁).obj t) ((Q₂).obj ((K).obj t)) rfl ((Q₀).obj s) ((Q₁).map g)) b b ha HEq.rfl
  have hmid := he.trans hr.symm
  have hfinal := hl.trans hmid
  exact hfinal

end OddMath.QuiverHecke
