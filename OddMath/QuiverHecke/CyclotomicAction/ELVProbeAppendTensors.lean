import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuotientTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendParity
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldInductionDotInverse

/-! # Generators of the scalar old-to-ordinary append comparison

The ordinary-probe generator transport in STATUS's remaining critical chain
item 3 requires the selected scalar append comparison. We compute its unit
and tensor generators through the canonical balanced-induction square, and
compare the signed dots used in DeformedActionAssembly §§5–6. All scalar
coefficients and the chosen ordinary probe category are retained.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory

namespace OddMath.QuiverHecke
universe u

section Cancellation
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

private theorem scalarComp_total_apply
    {F G H : Superfunctor k C (SVec k)} (f : F ⟶ G) (g : G ⟶ H)
    (w : C) (b : F.obj w) :
    (f ≫ g).total w b = g.total w (f.total w b) := by
  rw [Superfunctor.comp_total, SVec.comp_apply]

private theorem scalarComp_total
    {F G H : Superfunctor k C (SVec k)} (f : F ⟶ G) (g : G ⟶ H) (w : C) :
    (f ≫ g).total w = g.total w ∘ₗ f.total w :=
  Superfunctor.comp_total f g w

private theorem scalarTotal_congr
    {F G : Superfunctor k C (SVec k)} {f g : F ⟶ G} (h : f = g) (w : C) :
    f.total w = g.total w := congrArg (fun a : F ⟶ G => a.total w) h

private theorem scalarTensor_congr
    {E : Type u} [Category.{u} E] [Preadditive E] [Linear k E]
    (J : C ⥤ E) (M : Superfunctor k C (SVec k)) (v : C) (w : E)
    {g h : J.obj v ⟶ w} {b₀ b₁ : M.obj v}
    (hg : g = h) (hb : b₀ = b₁) :
    ELVOld.BalancedInduction.tensor J M.toFunctor v g b₀ =
      ELVOld.BalancedInduction.tensor J M.toFunctor v h b₁ :=
  congrArg₂ (fun a x => ELVOld.BalancedInduction.tensor J M.toFunctor v a x) hg hb

private theorem scalarIso_total_hom_inv
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (b : G.obj w) :
    e.hom.total w (e.inv.total w b) = b := by
  calc
    _ = (e.inv ≫ e.hom).total w b :=
      (scalarComp_total_apply e.inv e.hom w b).symm
    _ = (𝟙 G : G ⟶ G).total w b :=
      congrArg (fun f : G ⟶ G => f.total w b) e.inv_hom_id
    _ = b := by
      change ((LinearMap.id : G.obj w →ₗ[k] G.obj w) + 0) b = b
      rw [add_zero, LinearMap.id_apply]

private theorem scalarEqToHom_mem {F G : Superfunctor k C (SVec k)} (h : F = G) :
    (eqToHom h : F ⟶ G) ∈ parity (R := k) F G 0 := by
  subst G
  exact id_mem F

end Cancellation

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν

/-- The prescribed scalar quotient comparison is even. -/
theorem probeQuotientInducedModuleIso_hom_mem
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    (probeQuotientInducedModuleIso D Sc m ν N hN).hom ∈ parity (R := k) _ _ 0 := by
  let u := eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)
  let IQ := ELVOld.BalancedInduction.induction (k := k) Q
  have hu : u.inv ∈ parity (R := k) _ _ 0 :=
    scalarEqToHom_mem (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN).symm
  have hi : IQ.map u.inv ∈ parity (R := k) _ _ 0 := IsSuperfunctor.map_mem hu
  have hc : (probeQuotientCounitIso D Sc m ν
      (probeOrdinaryModuleSuperfunctor D Sc m ν N hN)).hom ∈ parity (R := k) _ _ 0 := by
    unfold probeQuotientCounitIso
    exact ELVOld.moduleIsoOfEvenNatIso_hom_mem _ _ _ _ _
  exact comp_mem hi hc

/-- The scalar quotient comparison cancels its canonical inverse unit tensor. -/
theorem probeQuotientInducedModuleIso_hom_unit
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (w : OrdinaryContentCategory D Sc a ν) (b : N.obj (probeOrdinaryOldObject D Sc m ν w)) :
    (probeQuotientInducedModuleIso D Sc m ν N hN).hom.app 0 w
      (ELVOld.BalancedInduction.tensor Q N.toFunctor
        (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b) = b := by
  let e := probeQuotientInducedModuleIso D Sc m ν N hN
  have h := probeQuotientInducedModuleIso_inv_tensor D Sc m ν N hN w b
  have hc := (congrArg (e.hom.total w) h).symm.trans
    (scalarIso_total_hom_inv e w b)
  have he : e.hom ∈ parity (R := k) _ _ 0 :=
    probeQuotientInducedModuleIso_hom_mem D Sc m ν N hN
  simpa only [SuperNatTrans.total,
    Superfunctor.app_eq_zero_of_mem he (q := 1) (by decide), add_zero] using hc

section Append
variable
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N) (i : I)
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "L" => ELVOld.BalancedInduction.induced J N
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν N hN
local notation "hL" => probeOldInduced_evaluatesCoefficients D m Sc ν i N hN

private def probeQuotientComparisonMap : (ELVOld.BalancedInduction.induction Q).obj N ⟶ O :=
  (probeQuotientInducedModuleIso D Sc m ν N hN).hom

local notation "S" => ELVOld.BalancedInduction.squareLinear J U Q T
  (probeOldOrdinaryFunctor_append D Sc m ν i) N O
  (probeQuotientComparisonMap D Sc m ν N hN)

private theorem probeAppend_hom_square :
    (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom =
      (probeQuotientInducedModuleIso D Sc m (i :: ν) L hL).inv ≫
        ELVOld.BalancedInduction.squareComparison J U Q T
          (probeOldOrdinaryFunctor_append D Sc m ν i) N O
          (probeQuotientInducedModuleIso D Sc m ν N hN).hom := by
  rw [ELVOld.BalancedInduction.squareComparison_eq]
  rfl

/-- The chosen comparison expressed on the literal old and ordinary coends.
This exposes identical module instances before computing generators. -/
def probeAppendComparisonLinear (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    ELVOld.BalancedInduction.Obj J N.toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj T (O).toFunctor ((U).obj w) :=
  (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom.total ((U).obj w)

private def probeAppendQuotientInverseLinear
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    ELVOld.BalancedInduction.Obj J N.toFunctor w →ₗ[k]
      ELVOld.BalancedInduction.Obj U (L).toFunctor ((U).obj w) :=
  (probeQuotientInducedModuleIso D Sc m (i :: ν) L hL).inv.total ((U).obj w)

private theorem probeAppendComparisonLinear_factor
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    probeAppendComparisonLinear D Sc m ν N hN i w =
      S ((U).obj w) ∘ₗ
        probeAppendQuotientInverseLinear D Sc m ν N hN i w := by
  exact (scalarTotal_congr (probeAppend_hom_square D Sc m ν N hN i) ((U).obj w)).trans
    (scalarComp_total _ _ ((U).obj w))

/-- The selected comparison on arbitrary old tensor generators. -/
theorem probeAppendOrdinaryModuleIso_hom_tensor
    (v : ELVOld.OldContentCategory D Sc cut ν)
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (g : (J).obj v ⟶ w) (b : N.obj v) :
    probeAppendComparisonLinear D Sc m ν N hN i w
      (ELVOld.BalancedInduction.tensor J N.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) ((U).map g) b := by
  let c := probeQuotientComparisonMap D Sc m ν N hN
  have h₁ : probeAppendQuotientInverseLinear D Sc m ν N hN i w
      (ELVOld.BalancedInduction.tensor J N.toFunctor v g b) =
      ELVOld.BalancedInduction.tensor U (L).toFunctor w (𝟙 ((U).obj w))
        (ELVOld.BalancedInduction.tensor J N.toFunctor v g b) :=
    probeQuotientInducedModuleIso_inv_tensor D Sc m (i :: ν) L hL
      ((U).obj w) (ELVOld.BalancedInduction.tensor J N.toFunctor v g b)
  have h₂ := ELVOld.BalancedInduction.squareLinear_tensor
    J U Q T (probeOldOrdinaryFunctor_append D Sc m ν i) N O
    (probeQuotientComparisonMap D Sc m ν N hN)
    (probeQuotientInducedModuleIso_hom_mem D Sc m ν N hN) v w g b
  have hunit : c.app 0 ((Q).obj v)
      (ELVOld.BalancedInduction.unit Q N.toFunctor v b) = b :=
    probeQuotientInducedModuleIso_hom_unit D Sc m ν N hN ((Q).obj v) b
  have hs : S ((U).obj w)
      (ELVOld.BalancedInduction.tensor U (L).toFunctor w (𝟙 ((U).obj w))
        (ELVOld.BalancedInduction.tensor J N.toFunctor v g b)) =
      ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) ((U).map g) b := by
    have ha : eqToHom (congrArg
        (fun F : ELVOld.OldContentCategory D Sc cut ν ⥤
            OrdinaryContentCategory D Sc a (i :: ν) => F.obj v)
        (probeOldOrdinaryFunctor_append D Sc m ν i)).symm ≫ (U).map g =
          (U).map g := by
      change 𝟙 ((U).obj ((J).obj v)) ≫ (U).map g = (U).map g
      exact Category.id_comp _
    exact h₂.trans (scalarTensor_congr T O ((Q).obj v) ((U).obj w) ha hunit)
  rw [probeAppendComparisonLinear_factor, LinearMap.comp_apply]
  calc
    _ = S ((U).obj w)
        (ELVOld.BalancedInduction.tensor U (L).toFunctor w (𝟙 ((U).obj w))
          (ELVOld.BalancedInduction.tensor J N.toFunctor v g b)) :=
      congrArg (S ((U).obj w)) h₁
    _ = _ := hs

/-- In particular, the chosen comparison intertwines the literal append units. -/
theorem probeAppendOrdinaryModuleIso_hom_unit
    (v : ELVOld.OldContentCategory D Sc cut ν) (b : N.obj v) :
    probeAppendComparisonLinear D Sc m ν N hN i ((J).obj v)
      (ELVOld.BalancedInduction.unit J N.toFunctor v b) =
      ELVOld.BalancedInduction.unit T (O).toFunctor ((Q).obj v) b := by
  have h := probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN i v ((J).obj v) (𝟙 _) b
  have hin := congrArg (probeAppendComparisonLinear D Sc m ν N hN i ((J).obj v))
    (ELVOld.BalancedInduction.unit_apply J N.toFunctor v b)
  have hout := ELVOld.BalancedInduction.unit_apply T (O).toFunctor ((Q).obj v) b
  exact hin.trans ((h.trans (congrArg
    (fun z => ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) z b)
    ((U).map_id ((J).obj v)))).trans hout.symm)

/-- The chosen comparison intertwines the prescribed signed induction dots,
including the odd twist on inhomogeneous coend arrows. -/
theorem probeAppendOrdinaryModuleIso_hom_dot
    (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    probeAppendComparisonLinear D Sc m ν N hN i w ∘ₗ
        probeOldContentInductionDot D Sc m ν i N w =
      ELVOld.BalancedInduction.transformLinear
        (probeOrdinaryAppendDot_supernatural D Sc m ν i) O ((U).obj w) ∘ₗ
        probeAppendComparisonLinear D Sc m ν N hN i w := by
  apply ELVOld.BalancedInduction.hom_ext
  intro v g b
  rw [LinearMap.comp_apply, probeOldContentInductionDot_tensor,
    probeAppendOrdinaryModuleIso_hom_tensor, LinearMap.comp_apply,
    probeAppendOrdinaryModuleIso_hom_tensor,
    ELVOld.BalancedInduction.transformLinear_tensor]
  have hg : (U).map (probeOldContentAppendDot D Sc m ν i v ≫ twist k (D.parity i) g) =
      probeOrdinaryAppendDot D Sc m ν i ((Q).obj v) ≫
        twist k (D.parity i) ((U).map g) := by
    rw [Functor.map_comp, probeOldContentAppendDot_image, map_twist]
    rfl
  exact congrArg (fun h => ELVOld.BalancedInduction.tensor T (O).toFunctor ((Q).obj v) h b) hg

end Append
end OddMath.QuiverHecke
