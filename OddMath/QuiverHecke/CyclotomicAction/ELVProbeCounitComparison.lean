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

private def probeTransposeLinear (R : Superfunctor k C (SVec k))
    (M : Superfunctor k E (SVec k))
    (c : R ⟶ (ELVOld.BalancedInduction.restriction A).obj M) (w : E) :
    ELVOld.BalancedInduction.Obj A R.toFunctor w →ₗ[k] M.obj w :=
  probeCounitLinear A M w ∘ₗ probeInducedMapLinear A c w

private theorem probeTransposeLinear_tensor (R : Superfunctor k C (SVec k))
    (M : Superfunctor k E (SVec k))
    (c : R ⟶ (ELVOld.BalancedInduction.restriction A).obj M)
    (hc : c ∈ parity (R := k) _ _ 0)
    (v : C) (w : E) (g : A.obj v ⟶ w) (b : R.obj v) :
    probeTransposeLinear A R M c w (ELVOld.BalancedInduction.tensor A R.toFunctor v g b) =
      M.map g (c.app 0 v b) := by
  unfold probeTransposeLinear
  rw [LinearMap.comp_apply, probeInducedMapLinear_tensor A c hc]
  exact probeCounitLinear_tensor A M v w g (c.app 0 v b)

private theorem probeInducedMapLinear_id (R : Superfunctor k C (SVec k)) (w : E) :
    probeInducedMapLinear A (𝟙 R) w = LinearMap.id := by
  apply ELVOld.BalancedInduction.hom_ext
  intro v g b
  have h := probeInducedMapLinear_tensor A (𝟙 R) (id_mem R) v w g b
  have hi : (𝟙 R : R ⟶ R).app 0 v b = b := rfl
  exact h.trans (congrArg (ELVOld.BalancedInduction.tensor A R.toFunctor v g) hi)

private theorem probeTransposeLinear_id (M : Superfunctor k E (SVec k)) (w : E) :
    probeTransposeLinear A ((ELVOld.BalancedInduction.restriction A).obj M) M (𝟙 _) w =
      probeCounitLinear A M w := by
  unfold probeTransposeLinear
  rw [probeInducedMapLinear_id, LinearMap.comp_id]

private theorem probeCompositeCounit
    {P₁ P₂ P₃ : Type u}
    [AddCommGroup P₁] [Module k P₁] [AddCommGroup P₂] [Module k P₂]
    [AddCommGroup P₃] [Module k P₃]
    (R : Superfunctor k C (SVec k)) (M : Superfunctor k E (SVec k)) (w : E)
    (c : R ⟶ (ELVOld.BalancedInduction.restriction A).obj M)
    (hc : c ∈ parity (R := k) _ _ 0)
    (f₀ : ELVOld.BalancedInduction.Obj A R.toFunctor w →ₗ[k] P₁)
    (f₁ : P₁ →ₗ[k] P₂) (f₂ : P₂ →ₗ[k] P₃) (f₃ : P₃ →ₗ[k] M.obj w)
    (h : ∀ (v : C) (g : A.obj v ⟶ w) (b : R.obj v),
      f₃ (f₂ (f₁ (f₀ (ELVOld.BalancedInduction.tensor A
        R.toFunctor v g b)))) = M.map g (c.app 0 v b)) :
    f₃ ∘ₗ f₂ ∘ₗ f₁ ∘ₗ f₀ = probeTransposeLinear A R M c w := by
  apply ELVOld.BalancedInduction.hom_ext
  intro v g b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  exact (h v g b).trans (probeTransposeLinear_tensor A R M c hc v w g b).symm

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
abbrev probeAppendOrdinaryCounitLinear
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
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
  trans probeTransposeLinear J R N (𝟙 R) w
  ·
    refine probeCompositeCounit J R N w (𝟙 R) (id_mem R)
      (probeAppendComparisonLinear D Sc m ν R hR i w)
      (probeInducedMapLinear T (eqToHom e) ((U).obj w))
      (probeCounitLinear T O ((U).obj w))
      (probeScalarValueLinear D Sc m ν i N hN w) ?_
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
    have hfinal := hvalue.trans (probeScalarValueLinear_apply D Sc m ν i N hN w (N.map g b))
    have hi : (𝟙 R : R ⟶ R).app 0 v b = b := rfl
    exact hfinal.trans (congrArg (N.map g) hi.symm)
  · exact probeTransposeLinear_id J N w

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
