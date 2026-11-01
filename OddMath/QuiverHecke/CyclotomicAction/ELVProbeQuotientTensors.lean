import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuotientInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientTensors

/-! # Tensor formulas for the scalar quotient induction comparison
The canonical unit and counit formulas compute the already constructed
comparison. The exact module restriction equality contributes identity
in parity zero and zero in parity one.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
section Components
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

theorem scalarModuleEqToHom_app {F G : Superfunctor k C (SVec k)} (h : F = G)
    (p : ZMod 2) (v : C) :
    (eqToHom h : F ⟶ G).app p v =
      if p = 0 then eqToHom (congrArg (fun N : Superfunctor k C (SVec k) => N.obj v) h) else 0 := by
  subst G
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp only [eqToHom_refl, Superfunctor.id_app_zero, ↓reduceIte]
  · simp only [eqToHom_refl, Superfunctor.id_app_one, one_ne_zero, ↓reduceIte]

private theorem scalarTensorIdentityAddZero
    {D' : Type u} [Category.{u} D'] [Preadditive D'] [Linear k D'] (J : C ⥤ D')
    (N : Superfunctor k C (SVec k)) (v : C) (w : D')
    (g h : J.obj v ⟶ w) (b : N.obj v) :
    ELVOld.BalancedInduction.tensor J N.toFunctor v g ((LinearMap.id : N.obj v →ₗ[k] N.obj v) b) +
      ELVOld.BalancedInduction.tensor J N.toFunctor v h ((0 : N.obj v →ₗ[k] N.obj v) b) =
        ELVOld.BalancedInduction.tensor J N.toFunctor v g b := by
  rw [LinearMap.id_apply, LinearMap.zero_apply,
    ELVOld.BalancedInduction.tensor_zero_right, add_zero]

end Components

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν

@[simp] theorem probeRestrictionEqToIso_hom_app
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) (p : ZMod 2)
    (v : ELVOld.OldContentCategory D Sc cut ν) :
    (eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)).hom.app p v =
      if p = 0 then LinearMap.id else 0 := by
  rw [eqToIso.hom, scalarModuleEqToHom_app]
  simp only [eqToHom_refl]
  rfl

theorem probeQuotientCounitIso_inv_total
    (M : Superfunctor k (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))
    (w : OrdinaryContentCategory D Sc a ν) :
    (probeQuotientCounitIso D Sc m ν M).inv.total w =
      ELVOld.BalancedInduction.unit Q (Q ⋙ M.toFunctor) (probeOrdinaryOldObject D Sc m ν w) :=
  ELVOld.moduleIsoOfEvenNatIso_inv_total _ _ _ _ _ w

/-- The inverse comparison is the literal unit tensor on the same old module vector. -/
theorem probeQuotientInducedModuleIso_inv_tensor
    (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (w : OrdinaryContentCategory D Sc a ν) (b : N.obj (probeOrdinaryOldObject D Sc m ν w)) :
    (probeQuotientInducedModuleIso D Sc m ν N hN).inv.total w b =
      ELVOld.BalancedInduction.tensor Q N.toFunctor
        (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b := by
  let S := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
  let u := eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)
  let c := probeQuotientCounitIso D Sc m ν S
  let IQ := ELVOld.BalancedInduction.induction (k := k) Q
  have hc : c.inv.total w b =
      ELVOld.BalancedInduction.tensor Q (probeOrdinaryRestriction D Sc m ν S).toFunctor
        (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b := by
    rw [probeQuotientCounitIso_inv_total]
    rfl
  have ht : (probeQuotientInducedModuleIso D Sc m ν N hN).inv.total w =
      (IQ.map u.hom).total w ∘ₗ c.inv.total w := by
    change (c.inv ≫ IQ.map u.hom).total w = _
    exact Superfunctor.comp_total _ _ w
  have hv : (probeQuotientInducedModuleIso D Sc m ν N hN).inv.total w b =
      (IQ.map u.hom).total w (c.inv.total w b) :=
    congrArg (fun f : S.obj w →ₗ[k] ELVOld.BalancedInduction.Obj Q N.toFunctor w => f b) ht
  refine hv.trans ?_
  refine (congrArg ((IQ.map u.hom).total w) hc).trans ?_
  change (ELVOld.BalancedInduction.moduleMap Q u.hom).total w
    (ELVOld.BalancedInduction.tensor Q (probeOrdinaryRestriction D Sc m ν S).toFunctor
      (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b) = _
  refine (ELVOld.BalancedInduction.moduleMap_total_tensor Q u.hom w
    (probeOrdinaryOldObject D Sc m ν w)
    (show (Q).obj (probeOrdinaryOldObject D Sc m ν w) ⟶ w from 𝟙 w) b).trans ?_
  simp only [u, probeRestrictionEqToIso_hom_app, ↓reduceIte, one_ne_zero]
  exact scalarTensorIdentityAddZero Q N (probeOrdinaryOldObject D Sc m ν w) w
    (show (Q).obj (probeOrdinaryOldObject D Sc m ν w) ⟶ w from 𝟙 w)
    (show (Q).obj (probeOrdinaryOldObject D Sc m ν w) ⟶ w from twist k 1 (𝟙 w)) b

end OddMath.QuiverHecke