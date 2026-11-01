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

private theorem probeIsoChainTotal
    {F₀ F₁ F₂ F₃ F₄ F₅ : Superfunctor k C (SVec k)}
    (e₁ : F₀ ≅ F₁) (e₂ : F₁ ≅ F₂) (e₃ : F₂ ≅ F₃)
    (e₄ : F₃ ≅ F₄) (e₅ : F₄ ≅ F₅) (w : C) (x : F₀.obj w) :
    (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅).hom.total w x =
      e₅.hom.total w (e₄.hom.total w (e₃.hom.total w
        (e₂.hom.total w (e₁.hom.total w x)))) := by
  simp only [Iso.trans_hom, Superfunctor.comp_total, SVec.comp_apply]

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
    (g : J.obj v ⟶ w) (b : M.obj v) :
    (ELVOld.BalancedInduction.moduleMap J f).total w
      (ELVOld.BalancedInduction.tensor J M.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor J L.toFunctor v g (f.app 0 v b) := by
  rw [ELVOld.BalancedInduction.moduleMap_total_tensor,
    Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide),
    LinearMap.zero_apply, ELVOld.BalancedInduction.tensor_zero_right, add_zero]

private theorem probeFlattenUnitTensor
    {E : Type u} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (K : D' ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (N : Superfunctor k C (SVec k)) (v : C) (t : D')
    (g : J.obj v ⟶ t) (b : N.obj v) :
    ((ELVOld.BalancedInduction.inductionComp J K).hom.app N).total (K.obj t)
      (ELVOld.BalancedInduction.tensor K (ELVOld.BalancedInduction.induced J N).toFunctor t
        (𝟙 (K.obj t)) (ELVOld.BalancedInduction.tensor J N.toFunctor v g b)) =
      ELVOld.BalancedInduction.tensor (J ⋙ K) N.toFunctor v (K.map g) b := by
  have h := ELVOld.BalancedInduction.inductionComp_hom_total_tensor J K N v t (K.obj t)
    (𝟙 (K.obj t)) g b
  exact h.trans (congrArg (fun z : K.obj (J.obj v) ⟶ K.obj t =>
    ELVOld.BalancedInduction.tensor (J ⋙ K) N.toFunctor v z b) (Category.comp_id (K.map g)))

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

/-- The chosen append comparison specializes the actual old Hom entry and
retains the same module vector on each balanced generator. -/
theorem probeAppendOrdinaryModuleIso_hom_tensor
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) (i : I)
    (v : ELVOld.OldContentCategory D Sc cut ν)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (g : (ELVOld.oldContentAppend D Sc cut ν i).obj v ⟶ t) (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total ((probeOldOrdinaryFunctor D Sc m (i :: ν)).obj t)
      (ELVOld.BalancedInduction.tensor (ELVOld.oldContentAppend D Sc cut ν i) N.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor (probeOrdinaryAppend D Sc m ν i)
        (probeOrdinaryModuleSuperfunctor D Sc m ν N hN).toFunctor
        ((probeOldOrdinaryFunctor D Sc m ν).obj v)
        (show (probeOrdinaryAppend D Sc m ν i).obj ((probeOldOrdinaryFunctor D Sc m ν).obj v) ⟶
          (probeOldOrdinaryFunctor D Sc m (i :: ν)).obj t from
          (probeOldOrdinaryFunctor D Sc m (i :: ν)).map g) b := by
  let J := ELVOld.oldContentAppend D Sc cut ν i
  let T := probeOrdinaryAppend D Sc m ν i
  let Q₀ := probeOldOrdinaryFunctor D Sc m ν
  let U := probeOldOrdinaryFunctor D Sc m (i :: ν)
  let L := ELVOld.BalancedInduction.induced J N
  let hL := probeOldInduced_evaluatesCoefficients D m Sc ν i N hN
  let O := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
  let f := probeQuotientInducedModuleIso D Sc m ν N hN
  let w := U.obj t
  let ot := t
  let γ : (J ⋙ U).obj v ⟶ w := U.map g
  let γ' : (Q₀ ⋙ T).obj v ⟶ w := γ
  let x := ELVOld.BalancedInduction.tensor J N.toFunctor v g b
  let y₁ := ELVOld.BalancedInduction.tensor U L.toFunctor ot (show U.obj ot ⟶ w from 𝟙 w) x
  let y₂ := ELVOld.BalancedInduction.tensor (J ⋙ U) N.toFunctor v γ b
  let y₃ := ELVOld.BalancedInduction.tensor (Q₀ ⋙ T) N.toFunctor v γ' b
  let inner := ELVOld.BalancedInduction.tensor Q₀ N.toFunctor v (𝟙 (Q₀.obj v)) b
  let y₄ := ELVOld.BalancedInduction.tensor T (ELVOld.BalancedInduction.induced Q₀ N).toFunctor
    (Q₀.obj v) γ' inner
  let y₅ := ELVOld.BalancedInduction.tensor T O.toFunctor (Q₀.obj v) γ' b
  let e₁ := (probeQuotientInducedModuleIso D Sc m (i :: ν) L hL).symm
  let e₂ := (ELVOld.BalancedInduction.inductionComp J U).app N
  let e₃ := ELVOld.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q₀ ⋙ T)
    (probeOldOrdinaryFunctor_append D Sc m ν i) N
  let e₄ := ((ELVOld.BalancedInduction.inductionComp Q₀ T).app N).symm
  let e₅ := (ELVOld.BalancedInduction.induction T).mapIso f
  have h₁ : e₁.hom.total w x = y₁ :=
    probeQuotientInducedModuleIso_inv_tensor D Sc m (i :: ν) L hL w x
  have h₂ : e₂.hom.total w y₁ = y₂ :=
    probeFlattenUnitTensor J U N v t g b
  have h₃ : e₃.hom.total w y₂ = y₃ := by
    have h := ELVOld.BalancedInduction.inducedIsoOfFunctorEq_tensor (J ⋙ U) (Q₀ ⋙ T)
      (probeOldOrdinaryFunctor_append D Sc m ν i) N v w γ b
    refine h.trans ?_
    have hg : eqToHom (congrArg (fun F : ELVOld.OldContentCategory D Sc cut ν ⥤
        OrdinaryContentCategory D Sc a (i :: ν) => F.obj v)
        (probeOldOrdinaryFunctor_append D Sc m ν i)).symm ≫ γ = γ' := by
      change 𝟙 ((Q₀ ⋙ T).obj v) ≫ γ' = γ'
      exact Category.id_comp γ'
    exact congrArg (fun z : (Q₀ ⋙ T).obj v ⟶ w =>
      ELVOld.BalancedInduction.tensor (Q₀ ⋙ T) N.toFunctor v z b) hg
  have h₄ : e₄.hom.total w y₃ = y₄ :=
    ELVOld.BalancedInduction.inductionComp_inv_total_tensor Q₀ T N v w γ' b
  have h₅ : e₅.hom.total w y₄ = y₅ := by
    have h := probeModuleMapEvenTensor T f.hom
      (probeQuotientInducedModuleIso_hom_even D Sc m ν N hN) w (Q₀.obj v) γ' inner
    refine h.trans ?_
    exact congrArg (ELVOld.BalancedInduction.tensor T O.toFunctor (Q₀.obj v) γ')
      (probeQuotientInducedModuleIso_hom_unit D Sc m ν N hN (Q₀.obj v) b)
  change (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅).hom.total w x = y₅
  refine (probeIsoChainTotal e₁ e₂ e₃ e₄ e₅ w x).trans ?_
  exact (congrArg (fun z => e₅.hom.total w (e₄.hom.total w (e₃.hom.total w (e₂.hom.total w z)))) h₁).trans
    ((congrArg (fun z => e₅.hom.total w (e₄.hom.total w (e₃.hom.total w z))) h₂).trans
      ((congrArg (fun z => e₅.hom.total w (e₄.hom.total w z)) h₃).trans
        ((congrArg (e₅.hom.total w) h₄).trans h₅)))

end OddMath.QuiverHecke