import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuotientTensors

/-! # Units of the scalar old-to-ordinary append comparison
The chosen comparison is first computed on coend units. The full generator
formula is then a consequence of module naturality.
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

private theorem probeFlattenUnits
    {E : Type u} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (K : D' ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (N : Superfunctor k C (SVec k)) (v : C) (b : N.obj v) :
    (probeFlattenModule J K N).total (K.obj (J.obj v))
      (ELVOld.BalancedInduction.unit K (ELVOld.BalancedInduction.induced J N).toFunctor
        (J.obj v) (ELVOld.BalancedInduction.unit J N.toFunctor v b)) =
      ELVOld.BalancedInduction.unit (J ⋙ K) N.toFunctor v b := by
  change (probeFlattenModule J K N).total (K.obj (J.obj v))
    (ELVOld.BalancedInduction.tensor K (ELVOld.BalancedInduction.induced J N).toFunctor
      (J.obj v) (𝟙 _) (ELVOld.BalancedInduction.tensor J N.toFunctor v (𝟙 _) b)) = _
  rw [probeFlattenUnitTensor, K.map_id]
  rfl

private theorem probeUnflattenUnits
    {E : Type u} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (K : D' ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (N : Superfunctor k C (SVec k)) (v : C) (b : N.obj v) :
    (probeUnflattenModule J K N).total ((J ⋙ K).obj v)
      (ELVOld.BalancedInduction.unit (J ⋙ K) N.toFunctor v b) =
      ELVOld.BalancedInduction.unit K (ELVOld.BalancedInduction.induced J N).toFunctor
        (J.obj v) (ELVOld.BalancedInduction.unit J N.toFunctor v b) :=
  probeUnflattenTensor J K N v ((J ⋙ K).obj v) (𝟙 _) b

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

private theorem probeAppendFlatten_unit
    (v : ELVOld.OldContentCategory D Sc cut ν) (b : N.obj v) :
    (probeFlattenModule J U N).total ((U).obj ((J).obj v))
      (ELVOld.BalancedInduction.unit U (L).toFunctor ((J).obj v)
        (ELVOld.BalancedInduction.unit J N.toFunctor v b)) =
      ELVOld.BalancedInduction.unit (J ⋙ U) N.toFunctor v b :=
  probeFlattenUnits J U N v b

private theorem probeAppendSquare_unit
    (v : ELVOld.OldContentCategory D Sc cut ν) (b : N.obj v) :
    (ELVOld.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
      (probeOldOrdinaryFunctor_append D Sc m ν i) N).hom.total ((U).obj ((J).obj v))
      (ELVOld.BalancedInduction.unit (J ⋙ U) N.toFunctor v b) =
      ELVOld.BalancedInduction.unit (Q ⋙ T) N.toFunctor v b := by
  have h := ELVOld.BalancedInduction.inducedIsoOfFunctorEq_tensor (J ⋙ U) (Q ⋙ T)
    (probeOldOrdinaryFunctor_append D Sc m ν i) N v ((U).obj ((J).obj v)) (𝟙 _) b
  refine h.trans ?_
  have hi : eqToHom (congrArg
      (fun F : ELVOld.OldContentCategory D Sc cut ν ⥤ B₊ => F.obj v)
      (probeOldOrdinaryFunctor_append D Sc m ν i)).symm ≫ 𝟙 ((U).obj ((J).obj v)) =
        𝟙 ((T).obj ((Q).obj v)) := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  exact congrArg (fun z : (Q ⋙ T).obj v ⟶ (Q ⋙ T).obj v =>
    ELVOld.BalancedInduction.tensor (Q ⋙ T) N.toFunctor v z b) hi

private theorem probeAppendUnflatten_unit
    (v : ELVOld.OldContentCategory D Sc cut ν) (b : N.obj v) :
    (probeUnflattenModule Q T N).total ((T).obj ((Q).obj v))
      (ELVOld.BalancedInduction.unit (Q ⋙ T) N.toFunctor v b) =
      ELVOld.BalancedInduction.unit T (ELVOld.BalancedInduction.induced Q N).toFunctor
        ((Q).obj v) (ELVOld.BalancedInduction.unit Q N.toFunctor v b) :=
  probeUnflattenUnits Q T N v b

/-- The selected old-to-ordinary append comparison on source coend units. -/
theorem probeAppendOrdinaryModuleIso_hom_unit
    (v : ELVOld.OldContentCategory D Sc cut ν) (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total ((U).obj ((J).obj v))
      (ELVOld.BalancedInduction.unit J N.toFunctor v b) =
      ELVOld.BalancedInduction.unit T (O).toFunctor ((Q).obj v) b := by
  change ((probeQuotientInducedModuleIso D Sc m (i :: ν) L
    (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN)).inv ≫
      probeFlattenModule J U N ≫
        (ELVOld.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
          (probeOldOrdinaryFunctor_append D Sc m ν i) N).hom ≫
            probeUnflattenModule Q T N ≫
              ELVOld.BalancedInduction.moduleMap T
                (probeQuotientInducedModuleIso D Sc m ν N hN).hom).total
    ((U).obj ((J).obj v)) (ELVOld.BalancedInduction.unit J N.toFunctor v b) = _
  simp only [Superfunctor.comp_total, SVec.comp_apply]
  rw [probeQuotientInducedModuleIso_inv_tensor, probeAppendFlatten_unit,
    probeAppendSquare_unit, probeAppendUnflatten_unit]
  exact (probeModuleMapEvenTensor T (probeQuotientInducedModuleIso D Sc m ν N hN).hom
    (probeQuotientInducedModuleIso_hom_even D Sc m ν N hN)
    ((T).obj ((Q).obj v)) ((Q).obj v) (𝟙 _)
    (ELVOld.BalancedInduction.unit Q N.toFunctor v b)).trans
      (congrArg (ELVOld.BalancedInduction.unit T (O).toFunctor ((Q).obj v))
        (probeQuotientInducedModuleIso_hom_unit D Sc m ν N hN ((Q).obj v) b))

end AppendMaps
end OddMath.QuiverHecke
