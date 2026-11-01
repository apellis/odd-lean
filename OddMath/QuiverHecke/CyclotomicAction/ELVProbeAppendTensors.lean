import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuotientTensors

/-! # Generators of the scalar old-to-ordinary append comparison
The existing five comparison isomorphisms are computed on the literal old
balanced tensor. No action on generators is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
section Comparison
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

private theorem probeMorphismChainTotal
    {F₀ F₁ F₂ F₃ F₄ F₅ : Superfunctor k C (SVec k)}
    (f₁ : F₀ ⟶ F₁) (f₂ : F₁ ⟶ F₂) (f₃ : F₂ ⟶ F₃)
    (f₄ : F₃ ⟶ F₄) (f₅ : F₄ ⟶ F₅) (w : C) (x : F₀.obj w) :
    (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅).total w x =
      f₅.total w (f₄.total w (f₃.total w (f₂.total w (f₁.total w x)))) := by
  simp only [Superfunctor.comp_total, SVec.comp_apply]

private theorem probeEvenIsoApp0AfterInv
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G)
    (he : e.hom ∈ parity (R := k) _ _ 0) (w : C) (b : G.obj w) :
    e.hom.app 0 w (e.inv.total w b) = b := by
  have ht : e.hom.total w ∘ₗ e.inv.total w = LinearMap.id := by
    calc
      _ = (e.inv ≫ e.hom).total w := (Superfunctor.comp_total _ _ w).symm
      _ = (fun f : G ⟶ G => f.total w) (𝟙 G) :=
        congrArg (fun f : G ⟶ G => f.total w) e.inv_hom_id
      _ = LinearMap.id := by
        change (LinearMap.id : G.obj w →ₗ[k] G.obj w) + 0 = LinearMap.id
        exact add_zero _
  have h := LinearMap.congr_fun ht b
  simpa only [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem he (q := 1) (by decide),
    add_zero, LinearMap.comp_apply, LinearMap.id_apply] using h

private theorem probeEqToHom_even {F G : Superfunctor k C (SVec k)} (h : F = G) :
    (eqToHom h : F ⟶ G) ∈ parity (R := k) F G 0 := by
  subst G
  exact id_mem F
end Comparison

section ModuleMap
variable {k : Type u} [CommRing k]
  {C D' : Type u} [Category.{u} C] [Category.{u} D']
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D'] [Linear k D'] [Supercategory k D']
  (J : C ⥤ D') [J.Additive] [J.Linear k] [IsSuperfunctor k J]

private theorem probeModuleMapEvenTensor
    {M L : Superfunctor k C (SVec k)} (f : M ⟶ L)
    (hf : f ∈ parity (R := k) _ _ 0) (w : D') (v : C)
    (g : (J).obj v ⟶ w) (b : M.obj v) :
    (ELVOld.BalancedInduction.moduleMap J f).total w
      (ELVOld.BalancedInduction.tensor J M.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor J (L).toFunctor v g (f.app 0 v b) := by
  rw [ELVOld.BalancedInduction.moduleMap_total_tensor,
    Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide),
    LinearMap.zero_apply, ELVOld.BalancedInduction.tensor_zero_right, add_zero]

private def probeFlattenModule
    {E : Type u} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (K : D' ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (N : Superfunctor k C (SVec k)) :
    ELVOld.BalancedInduction.induced K (ELVOld.BalancedInduction.induced J N) ⟶
      ELVOld.BalancedInduction.induced (J ⋙ K) N :=
  (ELVOld.BalancedInduction.inductionComp J K).hom.app N

private def probeUnflattenModule
    {E : Type u} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (K : D' ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (N : Superfunctor k C (SVec k)) :
    ELVOld.BalancedInduction.induced (J ⋙ K) N ⟶
      ELVOld.BalancedInduction.induced K (ELVOld.BalancedInduction.induced J N) :=
  (ELVOld.BalancedInduction.inductionComp J K).inv.app N

private theorem probeFlattenUnitTensor
    {E : Type u} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (K : D' ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (N : Superfunctor k C (SVec k)) (v : C) (t : D')
    (g : J.obj v ⟶ t) (b : N.obj v) :
    (probeFlattenModule J K N).total (K.obj t)
      (ELVOld.BalancedInduction.tensor K (ELVOld.BalancedInduction.induced J N).toFunctor t
        (𝟙 (K.obj t)) (ELVOld.BalancedInduction.tensor J N.toFunctor v g b)) =
      ELVOld.BalancedInduction.tensor (J ⋙ K) N.toFunctor v (K.map (X := J.obj v) (Y := t) g) b := by
  have h := ELVOld.BalancedInduction.inductionComp_hom_total_tensor J K N v t (K.obj t)
    (𝟙 (K.obj t)) g b
  exact h.trans (congrArg (fun z : K.obj (J.obj v) ⟶ K.obj t =>
    ELVOld.BalancedInduction.tensor (J ⋙ K) N.toFunctor v z b) (Category.comp_id (K.map (X := J.obj v) (Y := t) g)))

private theorem probeUnflattenTensor
    {E : Type u} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (K : D' ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (N : Superfunctor k C (SVec k)) (v : C) (w : E)
    (g : (J ⋙ K).obj v ⟶ w) (b : N.obj v) :
    (probeUnflattenModule J K N).total w
      (ELVOld.BalancedInduction.tensor (J ⋙ K) N.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor K (ELVOld.BalancedInduction.induced J N).toFunctor
        (J.obj v) g (ELVOld.BalancedInduction.tensor J N.toFunctor v (𝟙 (J.obj v)) b) :=
  ELVOld.BalancedInduction.inductionComp_inv_total_tensor J K N v w g b

end ModuleMap

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν

@[simp] theorem probeQuotientCounitIso_hom
    (M : Superfunctor k (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k)) :
    (probeQuotientCounitIso D Sc m ν M).hom =
      (ELVOld.BalancedInduction.adjunctionCounit Q).app M := by
  apply Superfunctor.hom_ext
  intro p v
  rfl

private theorem probeQuotientInducedModuleIso_hom_even
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    (probeQuotientInducedModuleIso D Sc m ν N hN).hom ∈ parity (R := k) _ _ 0 := by
  let u := eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)
  let IQ := ELVOld.BalancedInduction.induction (k := k) Q
  have hu : u.inv ∈ parity (R := k) _ _ 0 :=
    probeEqToHom_even (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN).symm
  have hi : IQ.map u.inv ∈ parity (R := k) _ _ 0 := IsSuperfunctor.map_mem hu
  have hc : (probeQuotientCounitIso D Sc m ν
      (probeOrdinaryModuleSuperfunctor D Sc m ν N hN)).hom ∈ parity (R := k) _ _ 0 := by
    rw [probeQuotientCounitIso_hom]
    exact ELVOld.BalancedInduction.adjunctionCounit_mem Q _
  exact comp_mem hi hc

private theorem probeQuotientInducedModuleIso_hom_unit
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (w : OrdinaryContentCategory D Sc a ν) (b : N.obj (probeOrdinaryOldObject D Sc m ν w)) :
    (probeQuotientInducedModuleIso D Sc m ν N hN).hom.app 0 w
      (ELVOld.BalancedInduction.tensor Q N.toFunctor (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b) = b := by
  let e := probeQuotientInducedModuleIso D Sc m ν N hN
  have h := probeQuotientInducedModuleIso_inv_tensor D Sc m ν N hN w b
  exact (congrArg (e.hom.app 0 w) h).symm.trans
    (probeEvenIsoApp0AfterInv e (probeQuotientInducedModuleIso_hom_even D Sc m ν N hN) w b)

section AppendMaps
variable
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) (i : I)
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "L" => ELVOld.BalancedInduction.induced J N
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν N hN
local notation "C₊" => ELVOld.OldContentCategory D Sc cut (i :: ν)
local notation "B₊" => OrdinaryContentCategory D Sc a (i :: ν)

private def probeAppendInsert (t : C₊) :
    ELVOld.BalancedInduction.Obj J N.toFunctor t →ₗ[k]
      ELVOld.BalancedInduction.Obj U (L).toFunctor ((U).obj t) :=
  (probeQuotientInducedModuleIso D Sc m (i :: ν) L
    (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN)).inv.total ((U).obj t)

private def probeAppendFlatten (w : B₊) :
    ELVOld.BalancedInduction.Obj U (L).toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj (J ⋙ U) N.toFunctor w :=
  (probeFlattenModule J U N).total w

private def probeAppendSquare (w : B₊) :
    ELVOld.BalancedInduction.Obj (J ⋙ U) N.toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj (Q ⋙ T) N.toFunctor w :=
  (ELVOld.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
    (probeOldOrdinaryFunctor_append D Sc m ν i) N).hom.total w

private def probeAppendUnflatten (w : B₊) :
    ELVOld.BalancedInduction.Obj (Q ⋙ T) N.toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj T (ELVOld.BalancedInduction.induced Q N).toFunctor w :=
  (probeUnflattenModule Q T N).total w

private def probeAppendDescend (w : B₊) :
    ELVOld.BalancedInduction.Obj T (ELVOld.BalancedInduction.induced Q N).toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj T (O).toFunctor w :=
  (ELVOld.BalancedInduction.moduleMap T
    (probeQuotientInducedModuleIso D Sc m ν N hN).hom).total w

/-- The chosen five canonical coend maps, with fixed raw tensor endpoints. -/
def probeAppendComparisonLinear (t : C₊) :
    ELVOld.BalancedInduction.Obj J N.toFunctor t →ₗ[k]
      ELVOld.BalancedInduction.Obj T (O).toFunctor ((U).obj t) :=
  probeAppendDescend D Sc m ν N hN i ((U).obj t) ∘ₗ
    probeAppendUnflatten D Sc m ν N i ((U).obj t) ∘ₗ
      probeAppendSquare D Sc m ν N i ((U).obj t) ∘ₗ
        probeAppendFlatten D Sc m ν N i ((U).obj t) ∘ₗ
          probeAppendInsert D Sc m ν N hN i t

private theorem probeAppendInsert_tensor
    (v : ELVOld.OldContentCategory D Sc cut ν) (t : C₊) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeAppendInsert D Sc m ν N hN i t (ELVOld.BalancedInduction.tensor J N.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor U (L).toFunctor t (𝟙 ((U).obj t))
        (ELVOld.BalancedInduction.tensor J N.toFunctor v g b) :=
  probeQuotientInducedModuleIso_inv_tensor D Sc m (i :: ν) L
    (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN) ((U).obj t) _

private theorem probeAppendFlatten_tensor
    (v : ELVOld.OldContentCategory D Sc cut ν) (t : C₊) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeAppendFlatten D Sc m ν N i ((U).obj t)
      (ELVOld.BalancedInduction.tensor U (L).toFunctor t (𝟙 ((U).obj t))
        (ELVOld.BalancedInduction.tensor J N.toFunctor v g b)) =
      ELVOld.BalancedInduction.tensor (J ⋙ U) N.toFunctor v ((U).map (X := (J).obj v) (Y := t) g) b :=
  probeFlattenUnitTensor (k := k)
    (C := ELVOld.OldContentCategory D Sc cut ν)
    (D' := ELVOld.OldContentCategory D Sc cut (i :: ν))
    (E := OrdinaryContentCategory D Sc a (i :: ν)) J U N v t g b

private theorem probeAppendSquare_tensor
    (v : ELVOld.OldContentCategory D Sc cut ν) (w : B₊)
    (g : (J ⋙ U).obj v ⟶ w) (b : N.obj v) :
    probeAppendSquare D Sc m ν N i w
      (ELVOld.BalancedInduction.tensor (J ⋙ U) N.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor (Q ⋙ T) N.toFunctor v
        (show (Q ⋙ T).obj v ⟶ w from g) b := by
  have h := ELVOld.BalancedInduction.inducedIsoOfFunctorEq_tensor (J ⋙ U) (Q ⋙ T)
    (probeOldOrdinaryFunctor_append D Sc m ν i) N v w g b
  refine h.trans ?_
  have hg : eqToHom (congrArg
      (fun F : ELVOld.OldContentCategory D Sc cut ν ⥤ B₊ => F.obj v)
      (probeOldOrdinaryFunctor_append D Sc m ν i)).symm ≫ g =
        (show (Q ⋙ T).obj v ⟶ w from g) := by
    change 𝟙 ((Q ⋙ T).obj v) ≫ (show (Q ⋙ T).obj v ⟶ w from g) = _
    exact Category.id_comp _
  exact congrArg (fun z : (Q ⋙ T).obj v ⟶ w =>
    ELVOld.BalancedInduction.tensor (Q ⋙ T) N.toFunctor v z b) hg

private theorem probeAppendUnflatten_tensor
    (v : ELVOld.OldContentCategory D Sc cut ν) (w : B₊)
    (g : (Q ⋙ T).obj v ⟶ w) (b : N.obj v) :
    probeAppendUnflatten D Sc m ν N i w
      (ELVOld.BalancedInduction.tensor (Q ⋙ T) N.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor T (ELVOld.BalancedInduction.induced Q N).toFunctor
        ((Q).obj v) g (ELVOld.BalancedInduction.tensor Q N.toFunctor v (𝟙 ((Q).obj v)) b) :=
  probeUnflattenTensor Q T N v w g b

private theorem probeAppendDescend_tensor
    (v : ELVOld.OldContentCategory D Sc cut ν) (w : B₊)
    (g : (T).obj ((Q).obj v) ⟶ w) (b : N.obj v) :
    probeAppendDescend D Sc m ν N hN i w
      (ELVOld.BalancedInduction.tensor T (ELVOld.BalancedInduction.induced Q N).toFunctor
        ((Q).obj v) g (ELVOld.BalancedInduction.tensor Q N.toFunctor v (𝟙 ((Q).obj v)) b)) =
      ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) g b := by
  have h := probeModuleMapEvenTensor T (probeQuotientInducedModuleIso D Sc m ν N hN).hom
    (probeQuotientInducedModuleIso_hom_even D Sc m ν N hN) w ((Q).obj v) g
    (ELVOld.BalancedInduction.tensor Q N.toFunctor v (𝟙 ((Q).obj v)) b)
  refine h.trans ?_
  exact congrArg (ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) g)
    (probeQuotientInducedModuleIso_hom_unit D Sc m ν N hN ((Q).obj v) b)

/-- The same five maps as a module morphism, using induced endpoints throughout. -/
def probeAppendComparisonMorphism :
    probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) L
      (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN) ⟶
        ELVOld.BalancedInduction.induced T O :=
  (probeQuotientInducedModuleIso D Sc m (i :: ν) L
    (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN)).inv ≫
      probeFlattenModule J U N ≫
        (ELVOld.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
          (probeOldOrdinaryFunctor_append D Sc m ν i) N).hom ≫
            probeUnflattenModule Q T N ≫
              ELVOld.BalancedInduction.moduleMap T (probeQuotientInducedModuleIso D Sc m ν N hN).hom

/-- Identify the chosen morphism before taking components or total maps. -/
theorem probeAppendComparisonMorphism_eq :
    probeAppendComparisonMorphism D Sc m ν N hN i =
      (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom := rfl

/-- The raw map is exactly the already chosen append comparison. -/
theorem probeAppendComparisonLinear_eq_total (t : C₊) :
    probeAppendComparisonLinear D Sc m ν N hN i t =
      (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total ((U).obj t) := by
  have ht : (probeAppendComparisonMorphism D Sc m ν N hN i).total ((U).obj t) =
      (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total ((U).obj t) :=
    congrArg (fun f : probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) L
      (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN) ⟶
        ELVOld.BalancedInduction.induced T O => f.total ((U).obj t))
      (probeAppendComparisonMorphism_eq D Sc m ν N hN i)
  have hn : (probeAppendComparisonMorphism D Sc m ν N hN i).total ((U).obj t) =
      probeAppendComparisonLinear D Sc m ν N hN i t := by
    apply LinearMap.ext
    intro x
    exact probeMorphismChainTotal
      (F₀ := probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) L
        (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN))
      (F₁ := ELVOld.BalancedInduction.induced U L)
      (F₂ := ELVOld.BalancedInduction.induced (J ⋙ U) N)
      (F₃ := ELVOld.BalancedInduction.induced (Q ⋙ T) N)
      (F₄ := ELVOld.BalancedInduction.induced T (ELVOld.BalancedInduction.induced Q N))
      (F₅ := ELVOld.BalancedInduction.induced T O)
      (probeQuotientInducedModuleIso D Sc m (i :: ν) L
        (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN)).inv
      (probeFlattenModule J U N)
      (ELVOld.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
        (probeOldOrdinaryFunctor_append D Sc m ν i) N).hom
      (probeUnflattenModule Q T N)
      (ELVOld.BalancedInduction.moduleMap T (probeQuotientInducedModuleIso D Sc m ν N hN).hom)
      ((U).obj t) x
  exact hn.symm.trans ht

/-- Scalar specialization of each actual old balanced generator. -/
theorem probeAppendComparisonLinear_tensor
    (v : ELVOld.OldContentCategory D Sc cut ν) (t : C₊) (g : (J).obj v ⟶ t) (b : N.obj v) :
    probeAppendComparisonLinear D Sc m ν N hN i t
      (ELVOld.BalancedInduction.tensor J N.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v)
        (show (T).obj ((Q).obj v) ⟶ (U).obj t from (U).map (X := (J).obj v) (Y := t) g) b := by
  unfold probeAppendComparisonLinear
  simp only [LinearMap.comp_apply]
  rw [probeAppendInsert_tensor, probeAppendFlatten_tensor, probeAppendSquare_tensor,
    probeAppendUnflatten_tensor, probeAppendDescend_tensor]

/-- The chosen comparison specializes the actual old Hom entry and retains
exactly the same module vector. -/
theorem probeAppendOrdinaryModuleIso_hom_tensor
    (v : ELVOld.OldContentCategory D Sc cut ν) (t : C₊) (g : (J).obj v ⟶ t) (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total ((U).obj t)
      (ELVOld.BalancedInduction.tensor J N.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v)
        (show (T).obj ((Q).obj v) ⟶ (U).obj t from (U).map (X := (J).obj v) (Y := t) g) b := by
  exact (congrArg (fun f : ELVOld.BalancedInduction.Obj J N.toFunctor t →ₗ[k]
      ELVOld.BalancedInduction.Obj T (O).toFunctor ((U).obj t) =>
        f (ELVOld.BalancedInduction.tensor J N.toFunctor v g b))
      (probeAppendComparisonLinear_eq_total D Sc m ν N hN i t)).symm.trans
    (probeAppendComparisonLinear_tensor D Sc m ν N hN i v t g b)

end AppendMaps
end OddMath.QuiverHecke