import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDottedComparison

/-! # The prescribed scalar dotted cap rows

DeformedMatrixComparison (2), (5) uses powers of the original signed dot
followed by the chosen ordinary counit. We compare these actual rows using
the selected append source comparison and canonical value isomorphism.
The old normalized kernel comparison, with its twisted actions and whole
output parity correction, remains the specified source of these module rows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

section CounitValues
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

private def capCounitLinear (M : Superfunctor k A (SVec k)) (w : A) :
    Obj J ((restriction J).obj M).toFunctor w →ₗ[k] M.obj w :=
  counit J M.toFunctor w

private theorem capCounitLinear_tensor (M : Superfunctor k A (SVec k))
    (w : A) (s : C) (g : J.obj s ⟶ w) (b : M.obj (J.obj s)) :
    capCounitLinear J M w (tensor J ((restriction J).obj M).toFunctor s g b) = M.map g b :=
  counit_tensor J M.toFunctor w s g b

/-- The chosen ordinary counit followed by a specified map of its value. -/
def ELVOld.BalancedInduction.counitValueLinear (M : Superfunctor k A (SVec k))
    (w : A) (P : SVec k) (v : M.obj w →ₗ[k] P) :
    Obj J ((restriction J).obj M).toFunctor w →ₗ[k] P :=
  v ∘ₗ capCounitLinear J M w

private theorem counitValueLinear_tensor (M : Superfunctor k A (SVec k))
    (w : A) (P : SVec k) (v : M.obj w →ₗ[k] P)
    (s : C) (g : J.obj s ⟶ w) (b : M.obj (J.obj s)) :
    counitValueLinear J M w P v (tensor J ((restriction J).obj M).toFunctor s g b) =
      v (M.map g b) := by
  unfold counitValueLinear
  rw [LinearMap.comp_apply, capCounitLinear_tensor]

private theorem capEqIso_mem {F G : Superfunctor k C (SVec k)} (h : F = G) :
    (eqToIso h).hom ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem F

end CounitValues

private theorem capCoendHom_ext
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

private theorem capCoendComp_ext
    {k C A V W : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    (f : Obj J M w →ₗ[k] V) (g : V →ₗ[k] W) (h : Obj J M w →ₗ[k] W)
    (hh : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      g (f (tensor J M s a b)) = h (tensor J M s a b)) : g ∘ₗ f = h := by
  apply capCoendHom_ext J M
  exact hh

private theorem dottedCapTransport
    {k V W Z : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid Z] [Module k Z]
    (C : V →ₗ[k] W) (f : Module.End k V) (g : Module.End k W)
    (a : V →ₗ[k] Z) (b : W →ₗ[k] Z)
    (h₀ : b ∘ₗ C = a) (hD : C ∘ₗ f = g ∘ₗ C) (n : ℕ) :
    b ∘ₗ (g ^ n) ∘ₗ C = a ∘ₗ (f ^ n) := by
  apply LinearMap.ext
  intro x
  have hp := intertwine_pow_apply C f g (fun x => LinearMap.congr_fun hD x) n x
  have hbase := LinearMap.congr_fun h₀ ((f ^ n) x)
  exact (congrArg b hp).symm.trans hbase

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "R" => Functor.obj (restriction J) N
local notation "hR" => probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
local notation "c" => eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)

/-- The value map is the specified scalar restriction equality on the old module. -/
def probeCapValueLinear
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (O).obj ((U).obj w) →ₗ[k] N.obj w :=
  (eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m (i :: ν) N hN)).hom.total w

/-- The chosen value comparison is identity on the original module vectors. -/
theorem probeCapValueLinear_apply
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν))
    (b : (O).obj ((U).obj w)) : probeCapValueLinear D Sc m ν i N hN w b = b := by
  unfold probeCapValueLinear
  simp only [SuperNatTrans.total, probeRestrictionEqToIso_hom_app,
    ↓reduceIte, one_ne_zero, add_zero]
  rfl

/-- The selected mapped append source comparison preserves the chosen ordinary
counit, with the canonical identity-on-vectors value isomorphism. -/
theorem probeMappedAppendLinear_counit
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    counitValueLinear T O ((U).obj w) (N.obj w) (probeCapValueLinear D Sc m ν i N hN w) ∘ₗ
        probeMappedAppendLinear D Sc m ν R hR ((restriction T).obj O) c i w =
      counit J N.toFunctor w := by
  apply capCoendComp_ext J (R).toFunctor
  intro s g b
  have hs := probeMateSourceComparisonLinear_tensor D Sc m ν i N hN s w g b
  have ht := counitValueLinear_tensor T O ((U).obj w) (N.obj w)
    (probeCapValueLinear D Sc m ν i N hN w) ((Q).obj s) ((U).map g) b
  have hv := probeCapValueLinear_apply D Sc m ν i N hN w ((O).map ((U).map g) b)
  have ha := LinearMap.congr_fun
    (probeScalarAction_old D Sc m (i :: ν) N hN ((J).obj s) w g) b
  have hpath := (congrArg (counitValueLinear T O ((U).obj w) (N.obj w)
    (probeCapValueLinear D Sc m ν i N hN w)) hs).trans (ht.trans (hv.trans ha))
  have ho := counit_tensor J N.toFunctor w s g b
  exact hpath.trans ho.symm

/-- Every prescribed dotted cap row uses the same chosen counit and original
signed dot power under the selected append/restriction comparison. -/
theorem probeMappedAppendLinear_capRow
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (n : ℕ) :
    counitValueLinear T O ((U).obj w) (N.obj w) (probeCapValueLinear D Sc m ν i N hN w) ∘ₗ
        ((transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i)
          ((restriction T).obj O) ((U).obj w)) ^ n) ∘ₗ
        probeMappedAppendLinear D Sc m ν R hR ((restriction T).obj O) c i w =
      counit J N.toFunctor w ∘ₗ ((probeOldContentInductionDot D Sc m ν i R w) ^ n) :=
  dottedCapTransport
    (probeMappedAppendLinear D Sc m ν R hR ((restriction T).obj O) c i w)
    (probeOldContentInductionDot D Sc m ν i R w)
    (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) ((restriction T).obj O) ((U).obj w))
    (counit J N.toFunctor w)
    (counitValueLinear T O ((U).obj w) (N.obj w) (probeCapValueLinear D Sc m ν i N hN w))
    (probeMappedAppendLinear_counit D Sc m ν i N hN w)
    (probeMappedAppendLinear_dot D Sc m ν R hR ((restriction T).obj O) c i
      (capEqIso_mem (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)) w) n

end OddMath.QuiverHecke
