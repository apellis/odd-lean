import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRestrictionComparison

/-! # The scalar append comparison preserves the ordinary counit

The ordinary-probe transport in STATUS critical-chain item 3 must compare
the selected adjunction of DeformedActionAssembly §5, as well as its dots.
The old append comparison, the literal restriction equality and the ordinary
quotient counit are computed on the same coend generators.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u

private theorem probeFunctionChain
    {P₀ P₁ P₂ P₃ : Type u} (f : P₀ → P₁) (g : P₁ → P₂) (h : P₂ → P₃)
    {x₀ : P₀} {x₁ : P₁} {x₂ : P₂} {x₃ : P₃}
    (h₁ : f x₀ = x₁) (h₂ : g x₁ = x₂) (h₃ : h x₂ = x₃) :
    h (g (f x₀)) = x₃ :=
  (congrArg (fun x => h (g x)) h₁).trans ((congrArg h h₂).trans h₃)

section ModuleMaps
variable {k : Type u} [CommRing k]
  {C E : Type u} [Category.{u} C] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (A : C ⥤ E) [A.Additive] [A.Linear k] [IsSuperfunctor k A]

private theorem probeEqToHom_mem
    {M L : Superfunctor k C (SVec k)} (h : M = L) :
    (eqToHom h : M ⟶ L) ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem M

private def probeInducedMapLinear
    {M L : Superfunctor k C (SVec k)} (f : M ⟶ L) (w : E) :
    ELVOld.BalancedInduction.Obj A M.toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj A L.toFunctor w :=
  (ELVOld.BalancedInduction.moduleMap A f).total w

private theorem probeInducedMapLinear_tensor
    {M L : Superfunctor k C (SVec k)} (f : M ⟶ L)
    (hf : f ∈ parity (R := k) _ _ 0) (v : C) (w : E)
    (g : A.obj v ⟶ w) (b : M.obj v) :
    probeInducedMapLinear A f w
      (ELVOld.BalancedInduction.tensor A M.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor A L.toFunctor v g (f.app 0 v b) :=
  ELVOld.BalancedInduction.moduleMap_total_tensor_even A f hf w v g b

private def probeCounitLinear (M : Superfunctor k E (SVec k)) (w : E) :
    ELVOld.BalancedInduction.Obj A
      ((ELVOld.BalancedInduction.restriction A).obj M).toFunctor w →ₗ[k] M.obj w :=
  ELVOld.BalancedInduction.counit A M.toFunctor w

private theorem probeCounitLinear_tensor (M : Superfunctor k E (SVec k))
    (v : C) (w : E) (g : A.obj v ⟶ w) (b : M.obj (A.obj v)) :
    probeCounitLinear A M w
      (ELVOld.BalancedInduction.tensor A
        ((ELVOld.BalancedInduction.restriction A).obj M).toFunctor v g b) =
      M.map g b :=
  ELVOld.BalancedInduction.counit_tensor A M.toFunctor w v g b

end ModuleMaps

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

private def probeScalarValueLinear
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    (probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN).obj ((U).obj w) →ₗ[k] N.obj w :=
  (eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m (i :: ν) N hN)).hom.total w

private theorem probeScalarValueLinear_apply
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (b : (probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN).obj ((U).obj w)) :
    probeScalarValueLinear D Sc m ν i N hN w b = b := by
  unfold probeScalarValueLinear
  simp only [SuperNatTrans.total, probeRestrictionEqToIso_hom_app,
    ↓reduceIte, one_ne_zero, add_zero]
  rfl

/-- Compose the selected scalar append comparison with the identity-on-vectors
restriction comparison and the literal ordinary adjunction counit. -/
def probeAppendOrdinaryCounitLinear
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    ELVOld.BalancedInduction.Obj J
      ((ELVOld.BalancedInduction.restriction J).obj N).toFunctor w →ₗ[k] N.obj w :=
  let R := (ELVOld.BalancedInduction.restriction J).obj N
  let hR := probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
  let O := probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
  let e := probeOrdinaryRestrictionModule_eq D Sc m ν i N hN
  probeScalarValueLinear D Sc m ν i N hN w ∘ₗ
    probeCounitLinear T O ((U).obj w) ∘ₗ
    probeInducedMapLinear T (eqToHom e) ((U).obj w) ∘ₗ
      probeAppendComparisonLinear D Sc m ν R hR i w

private theorem probeAppendOrdinaryCounitLinear_core
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    probeAppendOrdinaryCounitLinear D Sc m ν i N hN w =
      probeCounitLinear J N w := by
  let R := (ELVOld.BalancedInduction.restriction J).obj N
  let hR := probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
  let O := probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
  let e := probeOrdinaryRestrictionModule_eq D Sc m ν i N hN
  apply ELVOld.BalancedInduction.hom_ext
  intro v g b
  have h₁ := probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν R hR i v w g b
  have h₂ := probeInducedMapLinear_tensor T (eqToHom e) (probeEqToHom_mem e)
    ((Q).obj v) ((U).obj w) ((U).map g) b
  have hv : (eqToHom e).app 0 ((Q).obj v) b = b := by
    have ht := probeRestrictionEqToHom_app D Sc m ν i N hN 0 ((Q).obj v)
    have ht' : (eqToHom e).app 0 ((Q).obj v) = LinearMap.id := ht.trans (ite_eq_left rfl)
    exact (LinearMap.congr_fun ht' b).trans rfl
  have h₂' : probeInducedMapLinear T (eqToHom e) ((U).obj w)
      (ELVOld.BalancedInduction.tensor T
        (probeOrdinaryModuleSuperfunctor D Sc m ν R hR).toFunctor ((Q).obj v) ((U).map g) b) =
      ELVOld.BalancedInduction.tensor T
        ((ELVOld.BalancedInduction.restriction T).obj O).toFunctor
        ((Q).obj v) ((U).map g) b := by
    exact h₂.trans (congrArg (fun x => ELVOld.BalancedInduction.tensor T
      ((ELVOld.BalancedInduction.restriction T).obj O).toFunctor
      ((Q).obj v) ((U).map g) x) hv)
  have h₃ : probeCounitLinear T O ((U).obj w)
        (ELVOld.BalancedInduction.tensor T
          ((ELVOld.BalancedInduction.restriction T).obj O).toFunctor
          ((Q).obj v) ((U).map g) b) = N.map g b :=
    (probeCounitLinear_tensor T O ((Q).obj v) ((U).obj w) ((U).map g) b).trans
      (LinearMap.congr_fun (probeScalarAction_old D Sc m (i :: ν) N hN ((J).obj v) w g) b)
  have h := probeFunctionChain
    (probeAppendComparisonLinear D Sc m ν R hR i w)
    (probeInducedMapLinear T (eqToHom e) ((U).obj w))
    (probeCounitLinear T O ((U).obj w)) h₁ h₂' h₃
  have hvalue := congrArg (probeScalarValueLinear D Sc m ν i N hN w) h
  have hfinal := hvalue.trans
    ((probeScalarValueLinear_apply D Sc m ν i N hN w (N.map g b)).trans
      (probeCounitLinear_tensor J N v w g b).symm)
  set_option backward.dsimp.instances true in
    dsimp only [probeAppendOrdinaryCounitLinear]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  exact hfinal

/-- The chosen scalar comparison preserves the prescribed ordinary counit,
with no coefficient, dimension or homogeneity restriction on its generators. -/
theorem probeAppendOrdinaryCounitLinear_eq
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    probeAppendOrdinaryCounitLinear D Sc m ν i N hN w =
      ELVOld.BalancedInduction.counit J N.toFunctor w :=
  probeAppendOrdinaryCounitLinear_core D Sc m ν i N hN w

end OddMath.QuiverHecke
