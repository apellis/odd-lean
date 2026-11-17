import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.Algebra.SupermoduleIsoOfBijectiveTotals
import OddMath.QuiverHecke.CyclotomicAction.ContentModules.AppendQuotientTensors
import OddMath.QuiverHecke.CyclotomicAction.ProbeScalarModules.ProbeOrdinaryCategory
import OddMath.SKM.BWWPureNilpotent

/-!
# Probe mixed

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
    ELV.BalancedInduction.tensor J N.toFunctor v g ((LinearMap.id : N.obj v →ₗ[k] N.obj v) b) +
      ELV.BalancedInduction.tensor J N.toFunctor v h ((0 : N.obj v →ₗ[k] N.obj v) b) =
        ELV.BalancedInduction.tensor J N.toFunctor v g b := by
  rw [LinearMap.id_apply, LinearMap.zero_apply,
    ELV.BalancedInduction.tensor_zero_right, add_zero]

end Components

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν

@[simp] theorem probeRestrictionEqToIso_hom_app
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) (p : ZMod 2)
    (v : ELV.OldContentCategory D Sc cut ν) :
    (eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)).hom.app p v =
      if p = 0 then LinearMap.id else 0 := by
  rw [eqToIso.hom, scalarModuleEqToHom_app]
  simp only [eqToHom_refl]
  rfl

theorem probeQuotientCounitIso_inv_total
    (M : Superfunctor k (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))
    (w : OrdinaryContentCategory D Sc a ν) :
    (probeQuotientCounitIso D Sc m ν M).inv.total w =
      ELV.BalancedInduction.unit Q (Q ⋙ M.toFunctor) (probeOrdinaryOldObject D Sc m ν w) :=
  ELV.moduleIsoOfEvenNatIso_inv_total _ _ _ _ _ w

/-- The inverse comparison is the literal unit tensor on the same old module vector. -/
theorem probeQuotientInducedModuleIso_inv_tensor
    (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N)
    (w : OrdinaryContentCategory D Sc a ν) (b : N.obj (probeOrdinaryOldObject D Sc m ν w)) :
    (probeQuotientInducedModuleIso D Sc m ν N hN).inv.total w b =
      ELV.BalancedInduction.tensor Q N.toFunctor
        (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b := by
  let S := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
  let u := eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)
  let c := probeQuotientCounitIso D Sc m ν S
  let IQ := ELV.BalancedInduction.induction (k := k) Q
  have hc : c.inv.total w b =
      ELV.BalancedInduction.tensor Q (probeOrdinaryRestriction D Sc m ν S).toFunctor
        (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b := by
    rw [probeQuotientCounitIso_inv_total]
    rfl
  have ht : (probeQuotientInducedModuleIso D Sc m ν N hN).inv.total w =
      (IQ.map u.hom).total w ∘ₗ c.inv.total w := by
    change (c.inv ≫ IQ.map u.hom).total w = _
    exact Superfunctor.comp_total _ _ w
  have hv : (probeQuotientInducedModuleIso D Sc m ν N hN).inv.total w b =
      (IQ.map u.hom).total w (c.inv.total w b) :=
    congrArg (fun f : S.obj w →ₗ[k] ELV.BalancedInduction.Obj Q N.toFunctor w => f b) ht
  refine hv.trans ?_
  refine (congrArg ((IQ.map u.hom).total w) hc).trans ?_
  change (ELV.BalancedInduction.moduleMap Q u.hom).total w
    (ELV.BalancedInduction.tensor Q (probeOrdinaryRestriction D Sc m ν S).toFunctor
      (probeOrdinaryOldObject D Sc m ν w) (𝟙 w) b) = _
  refine (ELV.BalancedInduction.moduleMap_total_tensor Q u.hom w
    (probeOrdinaryOldObject D Sc m ν w)
    (show (Q).obj (probeOrdinaryOldObject D Sc m ν w) ⟶ w from 𝟙 w) b).trans ?_
  simp only [u, probeRestrictionEqToIso_hom_app, ↓reduceIte, one_ne_zero]
  exact scalarTensorIdentityAddZero Q N (probeOrdinaryOldObject D Sc m ν w) w
    (show (Q).obj (probeOrdinaryOldObject D Sc m ν w) ⟶ w from 𝟙 w)
    (show (Q).obj (probeOrdinaryOldObject D Sc m ν w) ⟶ w from twist k 1 (𝟙 w)) b

end OddMath.QuiverHecke
end

end

section

/-! # Scalar descent and restriction along append

The ordinary-probe comparison in STATUS critical-chain item 3 must retain the
chosen induction–restriction adjunction of DeformedActionAssembly §5. Scalar
coefficient evaluation is preserved by restriction, and the descended old
restriction equals literal ordinary restriction on the same vectors.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory

namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "cut" => probeCutoff D m
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m
local notation "J" => ELV.oldContentAppend D Sc cut ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)

/-- Restriction preserves the full scalar coefficient evaluation condition,
including the odd coefficient kernel. -/
theorem probeOldRestriction_evaluatesCoefficients
    (N : Superfunctor k (ELV.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N) :
    ProbeEvaluatesCoefficients D m Sc ν
      ((ELV.BalancedInduction.restriction J).obj N) := by
  intro v c
  change N.toFunctor.map ((J).map (probeOldCoefficient D m Sc ν v c)) = _
  rw [probeOldCoefficient_append]
  exact hN ((J).obj v) c

/-- Scalar descent commutes with the specified old and ordinary append
restrictions, as an equality of supermodules on the original vector values. -/
theorem probeOrdinaryRestrictionModule_eq
    (N : Superfunctor k (ELV.OldContentCategory D Sc cut (i :: ν)) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N) :
    probeOrdinaryModuleSuperfunctor D Sc m ν
      ((ELV.BalancedInduction.restriction J).obj N)
      (probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN) =
        (ELV.BalancedInduction.restriction T).obj
          (probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN) := by
  let R := (ELV.BalancedInduction.restriction J).obj N
  let hR := probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
  apply Superfunctor.ext
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro v
    rfl
  case h_map =>
    intro v w f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    let sv := probeOrdinaryOldObject D Sc m ν v
    let sw := probeOrdinaryOldObject D Sc m ν w
    obtain ⟨g, hg⟩ := elvProbeOldHom_surjective D m Sc v.word w.word f
    let g₀ : sv ⟶ sw := g
    have hq : (Q).map (X := sv) (Y := sw) g₀ = f := hg
    rw [← hq]
    have hs : (U).map (X := (J).obj sv) (Y := (J).obj sw)
        ((J).map (X := sv) (Y := sw) g₀) =
        (T).map (X := (Q).obj sv) (Y := (Q).obj sw)
          ((Q).map (X := sv) (Y := sw) g₀) :=
      elvProbeOldHom_rightContext D m Sc [i] sv.obj.word sw.obj.word g₀
    change probeOrdinaryModuleHom D m Sc ν R hR sv sw ((Q).map g₀) =
      probeOrdinaryModuleHom D m Sc (i :: ν) N hN ((J).obj sv) ((J).obj sw)
        ((T).map ((Q).map g₀))
    calc
      _ = R.toFunctor.map g₀ :=
        probeOrdinaryModuleHom_old D m Sc ν R hR sv sw g₀
      _ = N.toFunctor.map ((J).map g₀) := rfl
      _ = probeOrdinaryModuleHom D m Sc (i :: ν) N hN ((J).obj sv) ((J).obj sw)
          ((U).map ((J).map g₀)) :=
        (probeOrdinaryModuleHom_old D m Sc (i :: ν) N hN
          ((J).obj sv) ((J).obj sw) ((J).map g₀)).symm
      _ = _ := congrArg
        (probeOrdinaryModuleHom D m Sc (i :: ν) N hN ((J).obj sv) ((J).obj sw)) hs

end OddMath.QuiverHecke
end

end
