import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuotientTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitTensors

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

/-- The selected old-to-ordinary append comparison on source coend units. -/
theorem probeAppendOrdinaryModuleIso_hom_unit
    (v : ELVOld.OldContentCategory D Sc cut ν) (b : N.obj v) :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total ((U).obj ((J).obj v))
      (ELVOld.BalancedInduction.unit J N.toFunctor v b) =
      ELVOld.BalancedInduction.unit T (O).toFunctor ((Q).obj v) b := by
  let w : B₊ := (U).obj ((J).obj v)
  let x₀ := ELVOld.BalancedInduction.unit J N.toFunctor v b
  let a₁ : ELVOld.BalancedInduction.Obj J N.toFunctor ((J).obj v) →ₗ[k]
      ELVOld.BalancedInduction.Obj U (L).toFunctor w :=
    (probeQuotientInducedModuleIso D Sc m (i :: ν) L
      (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN)).inv.total w
  let a₂ : ELVOld.BalancedInduction.Obj U (L).toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj (J ⋙ U) N.toFunctor w :=
    ((ELVOld.BalancedInduction.inductionComp J U).hom.app N).total w
  let a₃ : ELVOld.BalancedInduction.Obj (J ⋙ U) N.toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj (Q ⋙ T) N.toFunctor w :=
    (ELVOld.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
      (probeOldOrdinaryFunctor_append D Sc m ν i) N).hom.total w
  let a₄ : ELVOld.BalancedInduction.Obj (Q ⋙ T) N.toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj T (ELVOld.BalancedInduction.induced Q N).toFunctor w :=
    ((ELVOld.BalancedInduction.inductionComp Q T).inv.app N).total w
  let a₅ : ELVOld.BalancedInduction.Obj T (ELVOld.BalancedInduction.induced Q N).toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj T (O).toFunctor w :=
    (ELVOld.BalancedInduction.moduleMap T
      (probeQuotientInducedModuleIso D Sc m ν N hN).hom).total w
  have he : (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom =
      (probeQuotientInducedModuleIso D Sc m (i :: ν) L
        (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN)).inv ≫
        (ELVOld.BalancedInduction.inductionComp J U).hom.app N ≫
          (ELVOld.BalancedInduction.inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T)
            (probeOldOrdinaryFunctor_append D Sc m ν i) N).hom ≫
            (ELVOld.BalancedInduction.inductionComp Q T).inv.app N ≫
              ELVOld.BalancedInduction.moduleMap T
                (probeQuotientInducedModuleIso D Sc m ν N hN).hom := rfl
  have hc : (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total w x₀ =
      a₅ (a₄ (a₃ (a₂ (a₁ x₀)))) := by
    rw [he]
    simp only [Superfunctor.comp_total, SVec.comp_apply, a₁, a₂, a₃, a₄, a₅]
  have ho : probeOrdinaryOldObject D Sc m (i :: ν) w = (J).obj v := rfl
  have hq := probeQuotientInducedModuleIso_inv_tensor D Sc m (i :: ν) L
    (probeOldInduced_evaluatesCoefficients D m Sc ν i N hN) w x₀
  have h₁ : a₁ x₀ = ELVOld.BalancedInduction.unit U (L).toFunctor ((J).obj v) x₀ := by
    have hq' : a₁ x₀ = ELVOld.BalancedInduction.tensor U (L).toFunctor ((J).obj v)
        (𝟙 w) x₀ := by
      simpa only [ho] using hq
    exact hq'.trans (ELVOld.BalancedInduction.unit_apply U (L).toFunctor ((J).obj v) x₀).symm
  have h₂ : a₂ (ELVOld.BalancedInduction.unit U (L).toFunctor ((J).obj v) x₀) =
      ELVOld.BalancedInduction.unit (J ⋙ U) N.toFunctor v b :=
    ELVOld.BalancedInduction.inductionComp_hom_total_unit J U N v b
  have h₃ : a₃ (ELVOld.BalancedInduction.unit (J ⋙ U) N.toFunctor v b) =
      ELVOld.BalancedInduction.unit (Q ⋙ T) N.toFunctor v b :=
    probeAppendSquare_unit D Sc m ν N i v b
  have h₄ : a₄ (ELVOld.BalancedInduction.unit (Q ⋙ T) N.toFunctor v b) =
      ELVOld.BalancedInduction.unit T (ELVOld.BalancedInduction.induced Q N).toFunctor
        ((Q).obj v) (ELVOld.BalancedInduction.unit Q N.toFunctor v b) := by
    have hi : ELVOld.BalancedInduction.unit (Q ⋙ T) N.toFunctor v b =
        ELVOld.BalancedInduction.tensor (Q ⋙ T) N.toFunctor v (𝟙 w) b :=
      ELVOld.BalancedInduction.unit_apply (Q ⋙ T) N.toFunctor v b
    have ht := ELVOld.BalancedInduction.inductionComp_inv_total_tensor Q T N v w (𝟙 w) b
    calc
      _ = a₄ (ELVOld.BalancedInduction.tensor (Q ⋙ T) N.toFunctor v (𝟙 w) b) :=
        congrArg a₄ hi
      _ = ELVOld.BalancedInduction.tensor T (ELVOld.BalancedInduction.induced Q N).toFunctor
          ((Q).obj v) (𝟙 w) (ELVOld.BalancedInduction.tensor Q N.toFunctor v (𝟙 _) b) := ht
      _ = ELVOld.BalancedInduction.tensor T (ELVOld.BalancedInduction.induced Q N).toFunctor
          ((Q).obj v) (𝟙 w) (ELVOld.BalancedInduction.unit Q N.toFunctor v b) :=
        congrArg (ELVOld.BalancedInduction.tensor T
          (ELVOld.BalancedInduction.induced Q N).toFunctor ((Q).obj v) (𝟙 w))
            (ELVOld.BalancedInduction.unit_apply Q N.toFunctor v b).symm
      _ = _ := (ELVOld.BalancedInduction.unit_apply T
        (ELVOld.BalancedInduction.induced Q N).toFunctor ((Q).obj v)
          (ELVOld.BalancedInduction.unit Q N.toFunctor v b)).symm
  have h₅ : a₅ (ELVOld.BalancedInduction.unit T
      (ELVOld.BalancedInduction.induced Q N).toFunctor ((Q).obj v)
      (ELVOld.BalancedInduction.unit Q N.toFunctor v b)) =
      ELVOld.BalancedInduction.unit T (O).toFunctor ((Q).obj v) b := by
    have hm := ELVOld.BalancedInduction.moduleMap_total_tensor_even T
      (probeQuotientInducedModuleIso D Sc m ν N hN).hom
      (probeQuotientInducedModuleIso_hom_even D Sc m ν N hN)
      w ((Q).obj v) (𝟙 w) (ELVOld.BalancedInduction.unit Q N.toFunctor v b)
    calc
      _ = a₅ (ELVOld.BalancedInduction.tensor T
          (ELVOld.BalancedInduction.induced Q N).toFunctor ((Q).obj v) (𝟙 w)
          (ELVOld.BalancedInduction.unit Q N.toFunctor v b)) :=
        congrArg a₅ (ELVOld.BalancedInduction.unit_apply T
          (ELVOld.BalancedInduction.induced Q N).toFunctor ((Q).obj v)
            (ELVOld.BalancedInduction.unit Q N.toFunctor v b))
      _ = ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) (𝟙 w)
          ((probeQuotientInducedModuleIso D Sc m ν N hN).hom.app 0 ((Q).obj v)
            (ELVOld.BalancedInduction.unit Q N.toFunctor v b)) := hm
      _ = ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) (𝟙 w) b :=
        congrArg (ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) (𝟙 w))
          (probeQuotientInducedModuleIso_hom_unit D Sc m ν N hN ((Q).obj v) b)
      _ = _ := (ELVOld.BalancedInduction.unit_apply T (O).toFunctor ((Q).obj v) b).symm
  exact hc.trans
    ((congrArg (fun z : ELVOld.BalancedInduction.Obj U (L).toFunctor w =>
      a₅ (a₄ (a₃ (a₂ z)))) h₁).trans
      ((congrArg (fun z : ELVOld.BalancedInduction.Obj (J ⋙ U) N.toFunctor w =>
        a₅ (a₄ (a₃ z))) h₂).trans
        ((congrArg (fun z : ELVOld.BalancedInduction.Obj (Q ⋙ T) N.toFunctor w =>
          a₅ (a₄ z)) h₃).trans
            ((congrArg a₅ h₄).trans h₅))))

end AppendMaps
end OddMath.QuiverHecke
