import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMateEvaluation

/-! # Ordered mate through the weighted quotient

DeformedMatrixComparison (2), (4) compares the prescribed cup-crossing-cap
mate. Its existing tensor evaluation retains the signed crossing and the
ordinary adjunction maps. The canonical restriction square identifies the
source of the selected append comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
section MateCarriers
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))

/-- The prescribed ordered mate on its literal restricted-module coend. -/
def orderedMateLinear (w : C) :
    BalancedInduction.Obj A ((BalancedInduction.restriction A).obj M).toFunctor w →ₗ[k]
      BalancedInduction.Obj A M.toFunctor (A.obj w) :=
  (BalancedInduction.orderedMateComponent A hα M).total w

omit [A.Additive] [A.Linear k] [IsSuperfunctor k A] in
private theorem tensor_neg_left (w v : C) (g : A.obj v ⟶ w) (b : M.obj v) :
    BalancedInduction.tensor A M.toFunctor v (-g) b = -BalancedInduction.tensor A M.toFunctor v g b := by
  unfold BalancedInduction.tensor
  rw [TensorProduct.neg_tmul, map_neg]

/-- The extra minus and the whole arrow twist of the ordered mate. -/
theorem orderedMateLinear_tensor (s w : C) (g : A.obj s ⟶ w) (b : M.obj (A.obj s)) :
    orderedMateLinear A hα M w
      (BalancedInduction.tensor A ((BalancedInduction.restriction A).obj M).toFunctor s g b) =
      -BalancedInduction.tensor A M.toFunctor (A.obj s) (α s ≫ twist k p (A.map g)) b :=
  BalancedInduction.orderedMateComponent_total_tensor A hα M s w g b
/-- The canonical output-object equality is retained as a final coend map. -/
def endpointMateLinear (w v : C) (e : A.obj w = v) :
    BalancedInduction.Obj A ((BalancedInduction.restriction A).obj M).toFunctor w →ₗ[k]
      BalancedInduction.Obj A M.toFunctor v :=
  BalancedInduction.postcompose A M.toFunctor (eqToHom e) ∘ₗ orderedMateLinear A hα M w

/-- At an identical endpoint this is exactly the existing ordered mate. -/
theorem endpointMateLinear_refl (w : C) :
    endpointMateLinear A hα M w (A.obj w) rfl = orderedMateLinear A hα M w := by
  dsimp only [endpointMateLinear]
  rw [eqToHom_refl, BalancedInduction.postcompose_id, LinearMap.id_comp]

theorem endpointMateLinear_tensor (w v : C) (e : A.obj w = v)
    (s : C) (g : A.obj s ⟶ w) (b : M.obj (A.obj s)) :
    endpointMateLinear A hα M w v e
      (BalancedInduction.tensor A ((BalancedInduction.restriction A).obj M).toFunctor s g b) =
      -BalancedInduction.tensor A M.toFunctor (A.obj s)
        ((α s ≫ twist k p (A.map g)) ≫ eqToHom e) b := by
  dsimp only [endpointMateLinear, LinearMap.comp_apply]
  rw [orderedMateLinear_tensor, map_neg, BalancedInduction.postcompose_tensor]

omit [A.Additive] [A.Linear k] [IsSuperfunctor k A] in
private def mateCoefficient (w v : C) (e : A.obj w = v)
    (s : C) (g : A.obj s ⟶ w) : (A ⋙ A).obj s ⟶ v :=
  (α s ≫ twist k p (A.map g)) ≫ eqToHom e

omit [A.Additive] [A.Linear k] [IsSuperfunctor k A] in
private def signedMateCoefficient (w v : C) (e : A.obj w = v)
    (s : C) (g : A.obj s ⟶ w) : (A ⋙ A).obj s ⟶ v :=
  -mateCoefficient (k := k) A (p := p) (α := α) w v e s g

/-- Writing the sign on the coefficient arrow fixes the raw coend operations
before applying a concrete quotient functor. -/
theorem endpointMateLinear_signed_tensor (w v : C) (e : A.obj w = v)
    (s : C) (g : A.obj s ⟶ w) (b : M.obj (A.obj s)) :
    endpointMateLinear A hα M w v e
      (BalancedInduction.tensor A ((BalancedInduction.restriction A).obj M).toFunctor s g b) =
      BalancedInduction.tensor A M.toFunctor (A.obj s)
        (signedMateCoefficient (k := k) A (p := p) (α := α) w v e s g) b :=
  (endpointMateLinear_tensor A hα M w v e s g b).trans
    (tensor_neg_left A M v (A.obj s) ((α s ≫ twist k p (A.map g)) ≫ eqToHom e) b).symm

end MateCarriers

private theorem coend_hom_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    {f g : BalancedInduction.Obj J M w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      f (BalancedInduction.tensor J M s a b) = g (BalancedInduction.tensor J M s a b)) : f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (BalancedInduction.relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

private theorem coend_comp_ext
    {k C A V W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    (f : BalancedInduction.Obj J M w →ₗ[k] V) (g : V →ₗ[k] Z)
    (h : BalancedInduction.Obj J M w →ₗ[k] W) (l : W →ₗ[k] Z)
    (hh : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      g (f (BalancedInduction.tensor J M s a b)) = l (h (BalancedInduction.tensor J M s a b))) :
    g ∘ₗ f = l ∘ₗ h := by
  apply coend_hom_ext J M
  exact hh

private theorem tensor_source_congr
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C]
    (A : C ⥤ C) (M : C ⥤ SVec k) (w v v' : C) (e : v = v')
    (g : A.obj v ⟶ w) (g' : A.obj v' ⟶ w)
    (b : M.obj v) (b' : M.obj v') (hg : HEq g g') (hb : HEq b b') :
    BalancedInduction.tensor A M v g b = BalancedInduction.tensor A M v' g' b' := by
  cases e
  cases hg
  cases hb
  rfl

private theorem negative_hom_heq {C : Type*} [Category* C] [Preadditive C]
    {a b a' b' : C} (ea : a = a') (eb : b = b')
    {f : a ⟶ b} {g : a' ⟶ b'} (h : HEq f g) : HEq (-f) (-g) := by
  cases ea
  cases eb
  cases h
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The old Rouquier mate is the given component of `oldModuleMate`. -/
def weightedOldMateLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J ((BalancedInduction.restriction J).obj RM).toFunctor w →ₗ[k]
      BalancedInduction.Obj J (RM).toFunctor ((J).obj w) :=
  ((CyclotomicCrossingTensor.oldModuleMate D Sc cutoff i).app
    (D.parity i * D.parity i) RM).total w

private theorem oldModuleMate_signed_tensor
    (L : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : L.obj ((J).obj s)) :
    ((CyclotomicCrossingTensor.oldModuleMate D Sc cutoff i).app
      (D.parity i * D.parity i) L).total w
      (BalancedInduction.tensor J ((BalancedInduction.restriction J).obj L).toFunctor s g b) =
      BalancedInduction.tensor J L.toFunctor ((J).obj s)
        (-(CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
          twist k (D.parity i * D.parity i) ((J).map g))) b :=
  (CyclotomicCrossingTensor.oldModuleMate_total_tensor D Sc cutoff i L s w g b).trans
    (tensor_neg_left J L ((J).obj w) ((J).obj s)
      (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i * D.parity i) ((J).map g)) b).symm

/-- Append comparison after the degree-zero part of a given input-module map. The input module is
kept independent so the literal coend dictionaries are fixed before restriction. -/
def weightedAppendSourceLinear
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (c : R ⟶ weightedRestriction D Sc cutoff N L) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J R.toFunctor w →ₗ[k]
      BalancedInduction.Obj T L.toFunctor ((Q).obj w) :=
  weightedAppendComparisonLinear D Sc cutoff N i L w ∘ₗ BalancedInduction.mapComponent J c 0 w

theorem weightedAppendSourceLinear_tensor
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (c : R ⟶ weightedRestriction D Sc cutoff N L)
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : R.obj s) :
    weightedAppendSourceLinear D Sc cutoff N i R L c w
      (BalancedInduction.tensor J R.toFunctor s g b) =
      BalancedInduction.tensor T L.toFunctor ((Q).obj s) ((Q).map g) (c.app 0 s b) := by
  have hm := BalancedInduction.mapComponent_tensor J c 0 w s g b
  have hx := hm.trans (congrArg (fun z => BalancedInduction.tensor J
    (weightedRestriction D Sc cutoff N L).toFunctor s z (c.app 0 s b)) (twist_zero g))
  exact (congrArg (weightedAppendComparisonLinear D Sc cutoff N i L w) hx).trans
    (appendWeightedModuleIso_hom_tensor D Sc cutoff N i L s w g (c.app 0 s b))

/-- The old prescribed mate after the degree-zero input map, with an independent coend source. -/
def weightedOldMatePrecomposeLinear
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J R.toFunctor w →ₗ[k]
      BalancedInduction.Obj J (RM).toFunctor ((J).obj w) :=
  weightedOldMateLinear D Sc cutoff N i M w ∘ₗ BalancedInduction.mapComponent J c 0 w

theorem weightedOldMatePrecomposeLinear_signed_tensor
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM)
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : R.obj s) :
    weightedOldMatePrecomposeLinear D Sc cutoff N i M R c w
      (BalancedInduction.tensor J R.toFunctor s g b) =
      BalancedInduction.tensor J (RM).toFunctor ((J).obj s)
        (-(CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
          twist k (D.parity i * D.parity i) ((J).map g))) (c.app 0 s b) := by
  have hm := BalancedInduction.mapComponent_tensor J c 0 w s g b
  have hx := hm.trans (congrArg (fun z => BalancedInduction.tensor J
    ((BalancedInduction.restriction J).obj RM).toFunctor s z (c.app 0 s b)) (twist_zero g))
  exact (congrArg (weightedOldMateLinear D Sc cutoff N i M w) hx).trans
    (oldModuleMate_signed_tensor D Sc cutoff i RM s w g (c.app 0 s b))

private theorem restrictionInv_comp_zero
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM) (s : OldCategory D Sc cutoff) (b : R.obj s) :
    (c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv).app 0 s b = c.app 0 s b := by
  change c.app 0 s b + 0 = c.app 0 s b
  exact add_zero _

/-- The strict append square retains its literal mapped arrow. -/
theorem oldTruncateFunctor_map_append (s w : OldCategory D Sc cutoff) (g : s ⟶ w) :
    (Q).map ((J).map g) = (T).map ((Q).map g) := by
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff s.word w.word).mkQ_surjective g
  rfl

/-- The ordered mate square after the degree-zero input component. The independent input
module fixes the literal coend dictionaries before restriction is specialized. -/
theorem weightedAppendMateSquare
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM) (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        weightedOldMatePrecomposeLinear D Sc cutoff N i M R c w =
      endpointMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i) M
        ((Q).obj w) ((Q).obj ((J).obj w)) rfl ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i R ((BalancedInduction.restriction T).obj M)
          (c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv) w := by
  apply coend_comp_ext J R.toFunctor
  intro s g b
  have ho := weightedOldMatePrecomposeLinear_signed_tensor D Sc cutoff N i M R c s w g b
  have hq := appendWeightedModuleIso_hom_tensor D Sc cutoff N i M ((J).obj s) ((J).obj w)
    (-(CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i * D.parity i) ((J).map g))) (c.app 0 s b)
  have hl := (congrArg (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w)) ho).trans hq
  have hs := weightedAppendSourceLinear_tensor D Sc cutoff N i R
    ((BalancedInduction.restriction T).obj M) (c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv) s w g b
  have ht := endpointMateLinear_signed_tensor T (truncatedEqualCross_supernatural D Sc cutoff N i) M
    ((Q).obj w) ((Q).obj ((J).obj w)) rfl ((Q).obj s) ((Q).map g) ((c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv).app 0 s b)
  have hr := (congrArg (endpointMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i)
    M ((Q).obj w) ((Q).obj ((J).obj w)) rfl) hs).trans ht
  let arrowNew := mateCoefficient (k := k) T (p := D.parity i * D.parity i)
    (α := truncatedEqualCrossComponent D Sc cutoff N i)
    ((Q).obj w) ((Q).obj ((J).obj w)) rfl ((Q).obj s) ((Q).map g)
  have hu : HEq ((Q).map (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i * D.parity i) ((J).map g))) arrowNew := by
    apply heq_of_eq
    dsimp only [arrowNew, mateCoefficient]
    rw [(Q).map_comp, map_twist, oldTruncateFunctor_map_equalCross, oldTruncateFunctor_map_append]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  have ha := (heq_of_eq ((Q).map_neg (f :=
    (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i * D.parity i) ((J).map g))))).trans
        (negative_hom_heq (show (Q).obj ((J).obj ((J).obj s)) =
          (T).obj ((T).obj ((Q).obj s)) from rfl) rfl hu)
  have hb := restrictionInv_comp_zero D Sc cutoff N i M R c s b
  have he := tensor_source_congr T M.toFunctor ((Q).obj ((J).obj w))
    ((Q).obj ((J).obj s)) ((T).obj ((Q).obj s)) rfl _
      (signedMateCoefficient (k := k) T (p := D.parity i * D.parity i)
        (α := truncatedEqualCrossComponent D Sc cutoff N i)
        ((Q).obj w) ((Q).obj ((J).obj w)) rfl ((Q).obj s) ((Q).map g))
      (c.app 0 s b) ((c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv).app 0 s b) ha (heq_of_eq hb.symm)
  have hmid := Eq.trans he (Eq.symm hr)
  have hfinal := Eq.trans hl hmid
  exact hfinal

/-- The selected comparison transports the given old mate with its canonical
restriction comparison. The input map is the identity, with no additional premise. -/
theorem appendWeightedModuleIso_hom_mate (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        weightedOldMatePrecomposeLinear D Sc cutoff N i M
          ((BalancedInduction.restriction J).obj RM) (𝟙 _) w =
      endpointMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i) M
        ((Q).obj w) ((Q).obj ((J).obj w)) rfl ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
          ((BalancedInduction.restriction T).obj M)
          ((𝟙 _) ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv) w :=
  weightedAppendMateSquare D Sc cutoff N i M ((BalancedInduction.restriction J).obj RM) (𝟙 _) w

end OddMath.QuiverHecke.ELVOld
