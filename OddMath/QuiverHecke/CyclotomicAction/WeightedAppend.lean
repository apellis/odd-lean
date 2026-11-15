import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.QuiverHecke.CyclotomicAction.OffDiagonalInput
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.ContentModule

/-!
# Weighted append

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Literal tensor generators of weighted append comparison

For DeformedActionAssembly §§5–6 and STATUS critical-chain item 2,
the selected old/truncated comparison preserves the input vector and sends
every old coend arrow to its literal quotient. No homogeneity restriction
is imposed on either tensor factor.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "F" => BalancedInduction.induced J RM
local notation "hF" => induced_killsWeightedCoefficients D Sc cutoff N i RM
  (weightedRestriction_kills D Sc cutoff N M)

private def appendQuotientCounit : (BalancedInduction.induction Q).obj RM ⟶ M :=
  (quotientInductionCounitIso D Sc cutoff N M).hom

local notation "S" => BalancedInduction.squareLinear J Q Q T
  (oldAppend_truncate D Sc cutoff N i) RM M (appendQuotientCounit D Sc cutoff N M)

private theorem appendWeightedModuleIso_hom_factor :
    (appendWeightedModuleIso D Sc cutoff N i M).hom =
      (quotientInducedWeightedModuleIso D Sc cutoff N F hF).inv ≫
        BalancedInduction.squareComparison J Q Q T (oldAppend_truncate D Sc cutoff N i)
          RM M (quotientInductionCounitIso D Sc cutoff N M).hom := by
  rw [BalancedInduction.squareComparison_eq]
  rfl

/-- The chosen comparison on the literal old and truncated coends.
The endpoint module instances are fixed before generator evaluation. -/
def weightedAppendComparisonLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (RM).toFunctor w →ₗ[k]
      BalancedInduction.Obj T M.toFunctor ((Q).obj w) :=
  (appendWeightedModuleIso D Sc cutoff N i M).hom.total ((Q).obj w)

private def appendQuotientInverseLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (RM).toFunctor w →ₗ[k]
      BalancedInduction.Obj Q (F).toFunctor ((Q).obj w) :=
  (quotientInducedWeightedModuleIso D Sc cutoff N F hF).inv.total ((Q).obj w)

private theorem weightedAppendComparisonLinear_factor (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M w =
      S ((Q).obj w) ∘ₗ appendQuotientInverseLinear D Sc cutoff N i M w := by
  exact (BalancedInduction.total_linear_congr
    (appendWeightedModuleIso_hom_factor D Sc cutoff N i M) ((Q).obj w)).trans
      (BalancedInduction.composition_total_linear _ _ ((Q).obj w))

/-- The selected five-isomorphism comparison sends the old tensor to the
truncated tensor with exactly the quotient arrow and unchanged vector. -/
theorem appendWeightedModuleIso_hom_tensor
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w)
    (b : M.obj ((Q).obj s)) :
    weightedAppendComparisonLinear D Sc cutoff N i M w
      (BalancedInduction.tensor J (RM).toFunctor s g b) =
      BalancedInduction.tensor T M.toFunctor ((Q).obj s) ((Q).map g) b := by
  have h₁ : appendQuotientInverseLinear D Sc cutoff N i M w
      (BalancedInduction.tensor J (RM).toFunctor s g b) =
      BalancedInduction.tensor Q (F).toFunctor w (𝟙 ((Q).obj w))
        (BalancedInduction.tensor J (RM).toFunctor s g b) :=
    quotientInducedWeightedModuleIso_inv_tensor D Sc cutoff N F hF ((Q).obj w)
      (BalancedInduction.tensor J (RM).toFunctor s g b)
  have h₂ := BalancedInduction.squareLinear_tensor J Q Q T
    (oldAppend_truncate D Sc cutoff N i) RM M (appendQuotientCounit D Sc cutoff N M)
    (quotientInductionCounitIso_hom_mem D Sc cutoff N M) s w g b
  have hs : S ((Q).obj w)
      (BalancedInduction.tensor Q (F).toFunctor w (𝟙 ((Q).obj w))
        (BalancedInduction.tensor J (RM).toFunctor s g b)) =
      BalancedInduction.tensor T M.toFunctor ((Q).obj s) ((Q).map g) b := by
    have hi : eqToHom (congrArg
        (fun H : OldCategory D Sc cutoff ⥤ TruncatedCategory D Sc cutoff N => H.obj s)
        (oldAppend_truncate D Sc cutoff N i)).symm ≫ (Q).map g = (Q).map g := by
      change 𝟙 _ ≫ (Q).map g = (Q).map g
      exact Category.id_comp _
    have hb : (appendQuotientCounit D Sc cutoff N M).app 0 ((Q).obj s)
        (BalancedInduction.unit Q (RM).toFunctor s b) = b := by
      change BalancedInduction.counit Q M.toFunctor ((Q).obj s)
        (BalancedInduction.unit Q (Q ⋙ M.toFunctor) s b) = b
      exact LinearMap.congr_fun (BalancedInduction.counit_unit Q M.toFunctor s) b
    exact h₂.trans (congrArg₂
      (fun z x => BalancedInduction.tensor T M.toFunctor ((Q).obj s) z x) hi hb)
  rw [weightedAppendComparisonLinear_factor, LinearMap.comp_apply]
  exact (congrArg (S ((Q).obj w)) h₁).trans hs

/-- The same selected comparison preserves the literal coend units. -/
theorem appendWeightedModuleIso_hom_unit
    (s : OldCategory D Sc cutoff) (b : M.obj ((Q).obj s)) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj s)
      (BalancedInduction.unit J (RM).toFunctor s b) =
      BalancedInduction.unit T M.toFunctor ((Q).obj s) b := by
  have h := appendWeightedModuleIso_hom_tensor D Sc cutoff N i M s ((J).obj s) (𝟙 _) b
  have hin := congrArg (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj s))
    (BalancedInduction.unit_apply J (RM).toFunctor s b)
  have hout := BalancedInduction.unit_apply T M.toFunctor ((Q).obj s) b
  exact hin.trans ((h.trans (congrArg
    (fun z => BalancedInduction.tensor T M.toFunctor ((Q).obj s) z b)
    ((Q).map_id ((J).obj s)))).trans hout.symm)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Ordinary adjunction under weighted append comparison

DeformedActionAssembly §§5–6 and STATUS critical-chain item 2 require
compatibility of the chosen
old/truncated append comparison with the ordinary adjunction maps.
Restriction commutes with the actual quotient by an even comparison
whose components are identities. The selected append comparison
intertwines the literal counits after that restriction comparison.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
section CounitCarriers
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (M : Superfunctor k D (SVec k))

/-- The ordinary counit on the literal coend of the restricted module. -/
def restrictionCounitLinear (w : D) :
    BalancedInduction.Obj J ((BalancedInduction.restriction J).obj M).toFunctor w →ₗ[k] M.obj w :=
  BalancedInduction.counit J M.toFunctor w

/-- This carrier realization is the prescribed ordinary counit. -/
theorem restrictionCounitLinear_apply (w : D)
    (b : BalancedInduction.Obj J ((BalancedInduction.restriction J).obj M).toFunctor w) :
    restrictionCounitLinear J M w b = BalancedInduction.counit J M.toFunctor w b := rfl

/-- The canonical counit evaluates its exact tensor arrow. -/
theorem restrictionCounitLinear_tensor (v : C) (w : D) (g : J.obj v ⟶ w)
    (b : M.obj (J.obj v)) :
    restrictionCounitLinear J M w
      (BalancedInduction.tensor J ((BalancedInduction.restriction J).obj M).toFunctor v g b) =
      M.map g b :=
  BalancedInduction.counit_tensor J M.toFunctor w v g b
end CounitCarriers

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- Pullback of truncated restriction and old restriction of pullback
are compared on the same module vector spaces. -/
def weightedAppendRestrictionIso :
    weightedRestriction D Sc cutoff N ((BalancedInduction.restriction T).obj M) ≅
      (BalancedInduction.restriction J).obj (weightedRestriction D Sc cutoff N M) :=
  moduleIsoOfEvenNatIso _ _
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun {v w} f => by
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
      rfl))
    (fun _ => id_mem _) (fun _ => id_mem _)

@[simp] theorem weightedAppendRestrictionIso_hom_app
    (p : ZMod 2) (s : OldCategory D Sc cutoff) :
    (weightedAppendRestrictionIso D Sc cutoff N i M).hom.app p s =
      if p = 0 then LinearMap.id else 0 := rfl

theorem weightedAppendRestrictionIso_hom_mem :
    (weightedAppendRestrictionIso D Sc cutoff N i M).hom ∈ parity (R := k) _ _ 0 := by
  unfold weightedAppendRestrictionIso
  exact moduleIsoOfEvenNatIso_hom_mem _ _ _ _ _

/-- The selected old/truncated append comparison carries the literal
ordinary counit to the truncated counit. The old-side source is identified
by the canonical even restriction-square comparison above. -/
theorem appendWeightedModuleIso_hom_counit (w : OldCategory D Sc cutoff) :
    restrictionCounitLinear T M ((Q).obj w) ∘ₗ
        weightedAppendComparisonLinear D Sc cutoff N i
          ((BalancedInduction.restriction T).obj M) w =
      restrictionCounitLinear J (weightedRestriction D Sc cutoff N M) w ∘ₗ
        BalancedInduction.mapComponent J
          (weightedAppendRestrictionIso D Sc cutoff N i M).hom 0 w := by
  apply BalancedInduction.hom_ext
  intro s g b
  let A := weightedRestriction D Sc cutoff N ((BalancedInduction.restriction T).obj M)
  let B := (BalancedInduction.restriction J).obj (weightedRestriction D Sc cutoff N M)
  let e := weightedAppendRestrictionIso D Sc cutoff N i M
  have ht := appendWeightedModuleIso_hom_tensor D Sc cutoff N i
    ((BalancedInduction.restriction T).obj M) s w g b
  have hT := restrictionCounitLinear_tensor T M ((Q).obj s) ((Q).obj w) ((Q).map g) b
  have hm := BalancedInduction.mapComponent_tensor J e.hom 0 w s g b
  have hb : e.hom.app 0 s b = b := rfl
  have hx : BalancedInduction.mapComponent J e.hom 0 w
      (BalancedInduction.tensor J A.toFunctor s g b) =
      BalancedInduction.tensor J B.toFunctor s g b := by
    refine hm.trans ?_
    exact congrArg₂ (fun z x => BalancedInduction.tensor J B.toFunctor s z x)
      (twist_zero g) hb
  have hJ := restrictionCounitLinear_tensor J (weightedRestriction D Sc cutoff N M) s w g b
  have hleft := (congrArg (restrictionCounitLinear T M ((Q).obj w)) ht).trans hT
  have hright :=
    (congrArg (restrictionCounitLinear J (weightedRestriction D Sc cutoff N M) w) hx).trans hJ
  exact hleft.trans hright.symm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The actual signed crossing mate on balanced generators

This evaluates the fixed old-module adjunction and the prescribed signed
crossing. No mate formula or component inverse is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem cross_eq (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    equalCrossOnDoubleInduction D Sc cutoff i N =
      BalancedInduction.doubleCrossComponent (append D Sc cutoff i)
        (equalCross_supernatural D Sc cutoff i) N := rfl

private theorem signedCross_component_eq (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (signedEqualInductionCross D Sc cutoff i).app (D.parity i * D.parity i) N =
      -BalancedInduction.doubleCrossComponent (append D Sc cutoff i)
        (equalCross_supernatural D Sc cutoff i) N := by
  rw [signedEqualInductionCross_app, ite_eq_left rfl]
  exact congrArg Neg.neg (cross_eq D Sc cutoff i N)

private theorem oldModuleMate_eq_ordered (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i) N =
      BalancedInduction.orderedMateComponent (append D Sc cutoff i)
        (equalCross_supernatural D Sc cutoff i) N := by
  rw [oldModuleMate_app, signedCross_component_eq]
  rfl

theorem oldModuleMate_total_tensor (i : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : N.obj ((append D Sc cutoff i).obj s)) :
    ((oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i) N).total t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj N).toFunctor s g b) =
    -BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor
      ((append D Sc cutoff i).obj s)
      (equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i * D.parity i) ((append D Sc cutoff i).map g)) b := by
  rw [oldModuleMate_eq_ordered]
  exact BalancedInduction.orderedMateComponent_total_tensor
    (append D Sc cutoff i) (equalCross_supernatural D Sc cutoff i) N s t g b

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # The actual odd mate is the normalized first crossing row

The fixed shiftedSourceParityIso twists the entire first tensor factor.
Co-Yoneda evaluation of the actual signed mate is minus toCyclotomic after
this canonical source isomorphism, on every vector and arbitrary endpoints.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem coend_total_ext
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M N : Superfunctor k C (SVec k)) (f : BalancedInduction.induced A M ⟶ N)
    (t : C) {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (e : N.obj t →ₗ[k] V) (r : W →ₗ[k] V)
    (J : BalancedInduction.Obj A M.toFunctor t →ₗ[k] W)
    (h : ∀ s (g : A.obj s ⟶ t) (b : M.obj s),
      e (f.total t (BalancedInduction.tensor A M.toFunctor s g b)) =
      -r (J (BalancedInduction.tensor A M.toFunctor s g b)))
    (z : BalancedInduction.Obj A M.toFunctor t) : e (f.total t z) = -r (J z) := by
  have hm : e.comp (SVec.toLinearMap (f.total t)) = -(r.comp J) := by
    apply BalancedInduction.hom_ext
    intro s g b
    change e (f.total t (BalancedInduction.tensor A M.toFunctor s g b)) =
      -r (J (BalancedInduction.tensor A M.toFunctor s g b))
    exact h s g b
  exact LinearMap.congr_fun hm z

private theorem parityCoefficientMap_one (i : I) (v : List I)
    (s : OldCategory D Sc cutoff)
    (b : ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj s) :
    (parityCoefficientMap D Sc cutoff i v).app 1 s b = b := by
  rw [parityCoefficientMap, Superfunctor.comp_app]
  simp only [coefficientModuleBackward_app, one_ne_zero, ↓reduceIte,
    SVec.zmod2_one_add_one, CategoryTheory.Limits.comp_zero, zero_add]
  rfl

theorem shiftedSourceParityIso_hom_total_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    (shiftedSourceParityIso D Sc cutoff i v).hom.total
      (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
    BalancedInduction.tensor (append D Sc cutoff i)
      (coefficientOneModule D Sc cutoff i v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff)
      (twist k 1 (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g) b := by
  rw [shiftedSourceParityIso_hom_eq_induction_map]
  change (BalancedInduction.moduleMap (append D Sc cutoff i)
    (parityCoefficientMap D Sc cutoff i v)).total _ _ = _
  rw [BalancedInduction.moduleMap_total_tensor]
  rw [Superfunctor.app_eq_zero_of_mem (parityCoefficientMap_mem D Sc cutoff i v)
    (show (0 : ZMod 2) ≠ 1 by decide)]
  simp only [SVec.zero_apply]
  rw [BalancedInduction.tensor_zero_right (append D Sc cutoff i)
    (coefficientOneModule D Sc cutoff i v).toFunctor
    (⟨s⟩ : OldCategory D Sc cutoff) g, zero_add,
    parityCoefficientMap_one D Sc cutoff i v (⟨s⟩ : OldCategory D Sc cutoff) b]

theorem shiftedSourceCanonicalEquiv_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    shiftedSourceCanonicalEquiv D Sc cutoff j v t
      (BalancedInduction.tensor (append D Sc cutoff j.1)
        ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b) =
    tensor D Sc cutoff j.1 v s t (oldTwist D Sc cutoff 1 (s ++ [j.1]) t g) b := by
  rw [shiftedSourceCanonicalEquiv_apply, shiftedSourceParityIso_hom_total_tensor,
    coefficientOneSourceEquiv_tensor]
  rw [oldCategory_twist]
  rfl

theorem pairing_eq_append_comp (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    pairing D Sc cutoff i v s t g b =
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) b ≫
      equalCrossComponent D Sc cutoff i (⟨s⟩ : OldCategory D Sc cutoff) ≫
      (append D Sc cutoff i).map (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff (s ++ [i]) t).mkQ_surjective g
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  rfl

theorem oldModuleMate_upper_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff i
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) =
    -((append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) b ≫
      equalCrossComponent D Sc cutoff i (⟨s⟩ : OldCategory D Sc cutoff) ≫
      twist k (D.parity i * D.parity i)
        ((append D Sc cutoff i).map
          (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
          (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g)) := by
  rw [oldModuleMate_total_tensor, map_neg]
  congr 1
  exact OldInductionRepresentable.upperHomEquiv_tensor D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    ((append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) _ b

theorem oldModuleMate_firstRow_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff j.1).app 1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff)
        (BalancedInduction.tensor (append D Sc cutoff j.1)
          ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) =
    -toCyclotomic D Sc cutoff j.1 v t
      (shiftedSourceCanonicalEquiv D Sc cutoff j v t
        (BalancedInduction.tensor (append D Sc cutoff j.1)
          ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor
          (⟨s⟩ : OldCategory D Sc cutoff) g b)) := by
  have hp : D.parity j.1 * D.parity j.1 = 1 := by rw [j.property]; decide
  have hc := congrArg (fun q => (oldModuleMate D Sc cutoff j.1).app q
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) hp.symm
  rw [hc, oldModuleMate_upper_tensor, shiftedSourceCanonicalEquiv_tensor,
    toCyclotomic_tensor, pairing_eq_append_comp]
  rw [hp]
  have ht := map_twist (R := k) (append D Sc cutoff j.1) 1
    (X := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
    (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g
  rw [oldCategory_twist] at ht
  have ht' :
      twist k 1 ((append D Sc cutoff j.1).map
        (X := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g) =
      (append D Sc cutoff j.1).map
        (X := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff))
        (oldTwist D Sc cutoff 1 (s ++ [j.1]) t g) := ht.symm
  exact congrArg (fun f => -((append D Sc cutoff j.1).map
    (X := (⟨v⟩ : OldCategory D Sc cutoff))
    (Y := (append D Sc cutoff j.1).obj (⟨s⟩ : OldCategory D Sc cutoff)) b ≫
    equalCrossComponent D Sc cutoff j.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ f)) ht' 

/-- The fixed actual odd mate is the already inverted crossing row after canonical J. -/
theorem oldModuleMate_firstRow (j : {j : I // D.parity j = 1}) (v t : List I)
    (z : (unshiftedSourceModule D Sc cutoff j.1 v).obj
      (⟨t⟩ : OldCategory D Sc cutoff)) :
    OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
      (((oldModuleMate D Sc cutoff j.1).app 1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total
        (⟨t⟩ : OldCategory D Sc cutoff) z) =
    -toCyclotomic D Sc cutoff j.1 v t (shiftedSourceCanonicalEquiv D Sc cutoff j v t z) := by
  exact coend_total_ext (append D Sc cutoff j.1)
    ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))))
    ((oldModuleMate D Sc cutoff j.1).app 1
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))
    (⟨t⟩ : OldCategory D Sc cutoff)
    (OldInductionRepresentable.upperHomEquiv D Sc cutoff j.1
      (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap
    (toCyclotomic D Sc cutoff j.1 v t)
    (shiftedSourceCanonicalEquiv D Sc cutoff j v t).toLinearMap
    (fun s g b => by
      cases s with
      | mk s => exact oldModuleMate_firstRow_tensor D Sc cutoff j v s t g b) z

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Weighted quotient comparison for a pair of appended strands

The same-colour crossing and mate comparison in DeformedActionAssembly §5
and DeformedMatrixComparison (2), (4) needs the canonical two-strand append
square. The pair preserves the complete weighted coefficient annihilator,
including odd generators, before the two canonical induction flattenings
are attached. The final comparison with iterated induction is separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i j : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "K" => CyclotomicCrossingTensor.append D Sc cutoff j
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "U" => truncatedAppend D Sc cutoff N [j]

/-- Successive old appends preserve the literal full coefficient basis. -/
theorem pairAppend_oldCoefficientBasis (v : List I) (a : SKM.SYM.CoefficientIndex D) :
    (J ⋙ K).map (oldCoefficientBasis D Sc cutoff v a) =
      oldCoefficientBasis D Sc cutoff (v ++ [i] ++ [j]) a := by
  rw [Functor.comp_map, append_oldCoefficientBasis, append_oldCoefficientBasis]

/-- The literal quotient square for two successive appends; no list-word
reassociation or content equivalence is inserted. -/
theorem pairAppend_truncate : (J ⋙ K) ⋙ Q = Q ⋙ (T ⋙ U) := by
  refine Functor.hext (F := (J ⋙ K) ⋙ Q) (G := Q ⋙ (T ⋙ U)) (fun _ => rfl) ?_
  intro v w f
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
  rfl

private theorem coefficient_slide_object
    {v w : OldCategory D Sc cutoff} (a : SKM.SYM.CoefficientIndex D) (g : v ⟶ w) :
    g ≫ oldCoefficientBasis D Sc cutoff w.word a =
      oldCoefficientBasis D Sc cutoff v.word a ≫ twist k (a.2.card : ZMod 2) g := by
  cases v
  cases w
  exact oldCoefficientBasis_slide D Sc cutoff _ _ a g

private theorem induced_kills_of_coefficient_image
    (L : OldCategory D Sc cutoff ⥤ OldCategory D Sc cutoff)
    [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (hL : ∀ (v : OldCategory D Sc cutoff) (a : SKM.SYM.CoefficientIndex D),
      L.map (oldCoefficientBasis D Sc cutoff v.word a) =
        oldCoefficientBasis D Sc cutoff (L.obj v).word a)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    KillsWeightedCoefficients D Sc cutoff N (BalancedInduction.induced L M) := by
  intro w a ha
  change BalancedInduction.postcompose L M.toFunctor
    (oldCoefficientBasis D Sc cutoff w a) = 0
  apply BalancedInduction.hom_ext
  intro v g b
  rw [BalancedInduction.postcompose_tensor, coefficient_slide_object, ← hL v a,
    BalancedInduction.balance]
  have hz : M.toFunctor.map (oldCoefficientBasis D Sc cutoff v.word a) = 0 := hM v.word a ha
  rw [hz, LinearMap.zero_apply]
  exact BalancedInduction.tensor_zero_right L M.toFunctor v _

/-- Induction along the successive-append functor preserves the exact
weighted coefficient annihilator. The input is any annihilated old module. -/
theorem pairInduced_killsWeightedCoefficients
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    KillsWeightedCoefficients D Sc cutoff N (BalancedInduction.induced (J ⋙ K) M) :=
  induced_kills_of_coefficient_image D Sc cutoff N (J ⋙ K)
    (fun v a => pairAppend_oldCoefficientBasis D Sc cutoff i j v.word a) M hM

section Comparison
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "JP" => J ⋙ K
local notation "TP" => T ⋙ U
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "FP" => BalancedInduction.induced JP RM
local notation "hFP" => pairInduced_killsWeightedCoefficients D Sc cutoff N i j RM
  (weightedRestriction_kills D Sc cutoff N M)

private def pairQuotientCounit : (BalancedInduction.induction Q).obj RM ⟶ M :=
  (quotientInductionCounitIso D Sc cutoff N M).hom

local notation "P" => BalancedInduction.squareLinear JP Q Q TP
  (pairAppend_truncate D Sc cutoff N i j) RM M (pairQuotientCounit D Sc cutoff N M)

end Comparison

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The equal-colour crossing through the weighted quotient

DeformedActionAssembly §5 and DeformedMatrixComparison (2), (4) require the
last-strand crossing, with the prescribed sign, on the chosen two-induction
comparison. The literal quotient of `crossLast` is identified with the
existing `crossTwo` append component under word associativity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- The crossing at the last two positions on successive singleton appends. -/
def truncatedEqualCrossComponent (s : TruncatedCategory D Sc cutoff N) :
    (T ⋙ T).obj s ⟶ (T ⋙ T).obj s :=
  (truncatedIdeal D Sc cutoff N _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i))

/-- Quotienting retains the literal affine crossing. -/
theorem oldTruncateFunctor_map_equalCross (s : OldCategory D Sc cutoff) :
    (Q).map (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s) =
      truncatedEqualCrossComponent D Sc cutoff N i ((Q).obj s) := rfl

/-- Full coefficient supernaturality descends from the old crossing. -/
theorem truncatedEqualCross_supernatural :
    IsSupernatural k (D.parity i * D.parity i)
      (truncatedEqualCrossComponent D Sc cutoff N i) := by
  apply IsSupernatural.of_twist
  · intro s
    exact Submodule.mem_map_of_mem
      (ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word i i))
  · intro s t f
    obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N s.word t.word).mkQ_surjective f
    let f' : (⟨s.word⟩ : OldCategory D Sc cutoff) ⟶ ⟨t.word⟩ :=
      (ideal D Sc cutoff s.word t.word).mkQ a
    have h := congrArg (fun g => (Q).map g)
      ((CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i).naturality_twist f')
    simp only [Functor.map_comp, map_twist] at h
    rw [map_twist]
    exact h

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Ordered mate through the weighted quotient

DeformedMatrixComparison (2), (4) compares the prescribed cup-crossing-cap
mate. Its existing tensor evaluation retains the signed crossing and the
ordinary adjunction maps. The canonical restriction square identifies the
source of the selected append comparison.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
section MateCarriers
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))

/-- The prescribed ordered mate on its literal restricted-module coend. -/
def orderedMateLinear (w : C) :
    BalancedInduction.Obj A ((BalancedInduction.restriction A).obj M).toFunctor w →ₗ[k]
      BalancedInduction.Obj A M.toFunctor (A.obj w) :=
  (BalancedInduction.orderedMateComponent A hα M).total w

omit [A.Additive] [A.Linear k] [IsSuperfunctor k A] in
private theorem tensor_neg_left (w v : C) (g : A.obj v ⟶ w) (b : M.obj v) :
    BalancedInduction.tensor A M.toFunctor v (-g) b = -BalancedInduction.tensor A M.toFunctor v g b := by
  unfold BalancedInduction.tensor
  rw [TensorProduct.neg_tmul, map_neg]

/-- The extra minus and the whole arrow twist of the ordered mate. -/
theorem orderedMateLinear_tensor (s w : C) (g : A.obj s ⟶ w) (b : M.obj (A.obj s)) :
    orderedMateLinear A hα M w
      (BalancedInduction.tensor A ((BalancedInduction.restriction A).obj M).toFunctor s g b) =
      -BalancedInduction.tensor A M.toFunctor (A.obj s) (α s ≫ twist k p (A.map g)) b :=
  BalancedInduction.orderedMateComponent_total_tensor A hα M s w g b
/-- The canonical output-object equality is retained as a final coend map. -/
def endpointMateLinear (w v : C) (e : A.obj w = v) :
    BalancedInduction.Obj A ((BalancedInduction.restriction A).obj M).toFunctor w →ₗ[k]
      BalancedInduction.Obj A M.toFunctor v :=
  BalancedInduction.postcompose A M.toFunctor (eqToHom e) ∘ₗ orderedMateLinear A hα M w

/-- At an identical endpoint this is exactly the existing ordered mate. -/
theorem endpointMateLinear_refl (w : C) :
    endpointMateLinear A hα M w (A.obj w) rfl = orderedMateLinear A hα M w := by
  dsimp only [endpointMateLinear]
  rw [eqToHom_refl, BalancedInduction.postcompose_id, LinearMap.id_comp]

theorem endpointMateLinear_tensor (w v : C) (e : A.obj w = v)
    (s : C) (g : A.obj s ⟶ w) (b : M.obj (A.obj s)) :
    endpointMateLinear A hα M w v e
      (BalancedInduction.tensor A ((BalancedInduction.restriction A).obj M).toFunctor s g b) =
      -BalancedInduction.tensor A M.toFunctor (A.obj s)
        ((α s ≫ twist k p (A.map g)) ≫ eqToHom e) b := by
  dsimp only [endpointMateLinear, LinearMap.comp_apply]
  rw [orderedMateLinear_tensor, map_neg, BalancedInduction.postcompose_tensor]

omit [A.Additive] [A.Linear k] [IsSuperfunctor k A] in
private def mateCoefficient (w v : C) (e : A.obj w = v)
    (s : C) (g : A.obj s ⟶ w) : (A ⋙ A).obj s ⟶ v :=
  (α s ≫ twist k p (A.map g)) ≫ eqToHom e

omit [A.Additive] [A.Linear k] [IsSuperfunctor k A] in
private def signedMateCoefficient (w v : C) (e : A.obj w = v)
    (s : C) (g : A.obj s ⟶ w) : (A ⋙ A).obj s ⟶ v :=
  -mateCoefficient (k := k) A (p := p) (α := α) w v e s g

/-- Writing the sign on the coefficient arrow fixes the raw coend operations
before applying a concrete quotient functor. -/
theorem endpointMateLinear_signed_tensor (w v : C) (e : A.obj w = v)
    (s : C) (g : A.obj s ⟶ w) (b : M.obj (A.obj s)) :
    endpointMateLinear A hα M w v e
      (BalancedInduction.tensor A ((BalancedInduction.restriction A).obj M).toFunctor s g b) =
      BalancedInduction.tensor A M.toFunctor (A.obj s)
        (signedMateCoefficient (k := k) A (p := p) (α := α) w v e s g) b :=
  (endpointMateLinear_tensor A hα M w v e s g b).trans
    (tensor_neg_left A M v (A.obj s) ((α s ≫ twist k p (A.map g)) ≫ eqToHom e) b).symm

end MateCarriers

private theorem coend_hom_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    {f g : BalancedInduction.Obj J M w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      f (BalancedInduction.tensor J M s a b) = g (BalancedInduction.tensor J M s a b)) : f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (BalancedInduction.relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

private theorem coend_comp_ext
    {k C A V W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    (f : BalancedInduction.Obj J M w →ₗ[k] V) (g : V →ₗ[k] Z)
    (h : BalancedInduction.Obj J M w →ₗ[k] W) (l : W →ₗ[k] Z)
    (hh : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      g (f (BalancedInduction.tensor J M s a b)) = l (h (BalancedInduction.tensor J M s a b))) :
    g ∘ₗ f = l ∘ₗ h := by
  apply coend_hom_ext J M
  exact hh

private theorem tensor_source_congr
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C]
    (A : C ⥤ C) (M : C ⥤ SVec k) (w v v' : C) (e : v = v')
    (g : A.obj v ⟶ w) (g' : A.obj v' ⟶ w)
    (b : M.obj v) (b' : M.obj v') (hg : HEq g g') (hb : HEq b b') :
    BalancedInduction.tensor A M v g b = BalancedInduction.tensor A M v' g' b' := by
  cases e
  cases hg
  cases hb
  rfl

private theorem negative_hom_heq {C : Type*} [Category* C] [Preadditive C]
    {a b a' b' : C} (ea : a = a') (eb : b = b')
    {f : a ⟶ b} {g : a' ⟶ b'} (h : HEq f g) : HEq (-f) (-g) := by
  cases ea
  cases eb
  cases h
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The old Rouquier mate is the given component of `oldModuleMate`. -/
def weightedOldMateLinear (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J ((BalancedInduction.restriction J).obj RM).toFunctor w →ₗ[k]
      BalancedInduction.Obj J (RM).toFunctor ((J).obj w) :=
  ((CyclotomicCrossingTensor.oldModuleMate D Sc cutoff i).app
    (D.parity i * D.parity i) RM).total w

private theorem oldModuleMate_signed_tensor
    (L : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : L.obj ((J).obj s)) :
    ((CyclotomicCrossingTensor.oldModuleMate D Sc cutoff i).app
      (D.parity i * D.parity i) L).total w
      (BalancedInduction.tensor J ((BalancedInduction.restriction J).obj L).toFunctor s g b) =
      BalancedInduction.tensor J L.toFunctor ((J).obj s)
        (-(CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
          twist k (D.parity i * D.parity i) ((J).map g))) b :=
  (CyclotomicCrossingTensor.oldModuleMate_total_tensor D Sc cutoff i L s w g b).trans
    (tensor_neg_left J L ((J).obj w) ((J).obj s)
      (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i * D.parity i) ((J).map g)) b).symm

/-- Append comparison after the degree-zero part of a given input-module map. The input module is
kept independent so the literal coend dictionaries are fixed before restriction. -/
def weightedAppendSourceLinear
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (c : R ⟶ weightedRestriction D Sc cutoff N L) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J R.toFunctor w →ₗ[k]
      BalancedInduction.Obj T L.toFunctor ((Q).obj w) :=
  weightedAppendComparisonLinear D Sc cutoff N i L w ∘ₗ BalancedInduction.mapComponent J c 0 w

theorem weightedAppendSourceLinear_tensor
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (c : R ⟶ weightedRestriction D Sc cutoff N L)
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : R.obj s) :
    weightedAppendSourceLinear D Sc cutoff N i R L c w
      (BalancedInduction.tensor J R.toFunctor s g b) =
      BalancedInduction.tensor T L.toFunctor ((Q).obj s) ((Q).map g) (c.app 0 s b) := by
  have hm := BalancedInduction.mapComponent_tensor J c 0 w s g b
  have hx := hm.trans (congrArg (fun z => BalancedInduction.tensor J
    (weightedRestriction D Sc cutoff N L).toFunctor s z (c.app 0 s b)) (twist_zero g))
  exact (congrArg (weightedAppendComparisonLinear D Sc cutoff N i L w) hx).trans
    (appendWeightedModuleIso_hom_tensor D Sc cutoff N i L s w g (c.app 0 s b))

/-- The old prescribed mate after the degree-zero input map, with an independent coend source. -/
def weightedOldMatePrecomposeLinear
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J R.toFunctor w →ₗ[k]
      BalancedInduction.Obj J (RM).toFunctor ((J).obj w) :=
  weightedOldMateLinear D Sc cutoff N i M w ∘ₗ BalancedInduction.mapComponent J c 0 w

theorem weightedOldMatePrecomposeLinear_signed_tensor
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM)
    (s w : OldCategory D Sc cutoff) (g : (J).obj s ⟶ w) (b : R.obj s) :
    weightedOldMatePrecomposeLinear D Sc cutoff N i M R c w
      (BalancedInduction.tensor J R.toFunctor s g b) =
      BalancedInduction.tensor J (RM).toFunctor ((J).obj s)
        (-(CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
          twist k (D.parity i * D.parity i) ((J).map g))) (c.app 0 s b) := by
  have hm := BalancedInduction.mapComponent_tensor J c 0 w s g b
  have hx := hm.trans (congrArg (fun z => BalancedInduction.tensor J
    ((BalancedInduction.restriction J).obj RM).toFunctor s z (c.app 0 s b)) (twist_zero g))
  exact (congrArg (weightedOldMateLinear D Sc cutoff N i M w) hx).trans
    (oldModuleMate_signed_tensor D Sc cutoff i RM s w g (c.app 0 s b))

private theorem restrictionInv_comp_zero
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM) (s : OldCategory D Sc cutoff) (b : R.obj s) :
    (c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv).app 0 s b = c.app 0 s b := by
  change c.app 0 s b + 0 = c.app 0 s b
  exact add_zero _

/-- The strict append square retains its literal mapped arrow. -/
theorem oldTruncateFunctor_map_append (s w : OldCategory D Sc cutoff) (g : s ⟶ w) :
    (Q).map ((J).map g) = (T).map ((Q).map g) := by
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff s.word w.word).mkQ_surjective g
  rfl

/-- The ordered mate square after the degree-zero input component. The independent input
module fixes the literal coend dictionaries before restriction is specialized. -/
theorem weightedAppendMateSquare
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (c : R ⟶ (BalancedInduction.restriction J).obj RM) (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        weightedOldMatePrecomposeLinear D Sc cutoff N i M R c w =
      endpointMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i) M
        ((Q).obj w) ((Q).obj ((J).obj w)) rfl ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i R ((BalancedInduction.restriction T).obj M)
          (c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv) w := by
  apply coend_comp_ext J R.toFunctor
  intro s g b
  have ho := weightedOldMatePrecomposeLinear_signed_tensor D Sc cutoff N i M R c s w g b
  have hq := appendWeightedModuleIso_hom_tensor D Sc cutoff N i M ((J).obj s) ((J).obj w)
    (-(CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i * D.parity i) ((J).map g))) (c.app 0 s b)
  have hl := (congrArg (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w)) ho).trans hq
  have hs := weightedAppendSourceLinear_tensor D Sc cutoff N i R
    ((BalancedInduction.restriction T).obj M) (c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv) s w g b
  have ht := endpointMateLinear_signed_tensor T (truncatedEqualCross_supernatural D Sc cutoff N i) M
    ((Q).obj w) ((Q).obj ((J).obj w)) rfl ((Q).obj s) ((Q).map g) ((c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv).app 0 s b)
  have hr := (congrArg (endpointMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i)
    M ((Q).obj w) ((Q).obj ((J).obj w)) rfl) hs).trans ht
  let arrowNew := mateCoefficient (k := k) T (p := D.parity i * D.parity i)
    (α := truncatedEqualCrossComponent D Sc cutoff N i)
    ((Q).obj w) ((Q).obj ((J).obj w)) rfl ((Q).obj s) ((Q).map g)
  have hu : HEq ((Q).map (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i * D.parity i) ((J).map g))) arrowNew := by
    apply heq_of_eq
    dsimp only [arrowNew, mateCoefficient]
    rw [(Q).map_comp, map_twist, oldTruncateFunctor_map_equalCross, oldTruncateFunctor_map_append]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  have ha := (heq_of_eq ((Q).map_neg (f :=
    (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i * D.parity i) ((J).map g))))).trans
        (negative_hom_heq (show (Q).obj ((J).obj ((J).obj s)) =
          (T).obj ((T).obj ((Q).obj s)) from rfl) rfl hu)
  have hb := restrictionInv_comp_zero D Sc cutoff N i M R c s b
  have he := tensor_source_congr T M.toFunctor ((Q).obj ((J).obj w))
    ((Q).obj ((J).obj s)) ((T).obj ((Q).obj s)) rfl _
      (signedMateCoefficient (k := k) T (p := D.parity i * D.parity i)
        (α := truncatedEqualCrossComponent D Sc cutoff N i)
        ((Q).obj w) ((Q).obj ((J).obj w)) rfl ((Q).obj s) ((Q).map g))
      (c.app 0 s b) ((c ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv).app 0 s b) ha (heq_of_eq hb.symm)
  have hmid := Eq.trans he (Eq.symm hr)
  have hfinal := Eq.trans hl hmid
  exact hfinal

/-- The selected comparison transports the given old mate with its canonical
restriction comparison. The input map is the identity, with no additional premise. -/
theorem appendWeightedModuleIso_hom_mate (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        weightedOldMatePrecomposeLinear D Sc cutoff N i M
          ((BalancedInduction.restriction J).obj RM) (𝟙 _) w =
      endpointMateLinear T (truncatedEqualCross_supernatural D Sc cutoff N i) M
        ((Q).obj w) ((Q).obj ((J).obj w)) rfl ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
          ((BalancedInduction.restriction T).obj M)
          ((𝟙 _) ≫ (weightedAppendRestrictionIso D Sc cutoff N i M).inv) w :=
  weightedAppendMateSquare D Sc cutoff N i M ((BalancedInduction.restriction J).obj RM) (𝟙 _) w

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Source and target charts for weighted matrix transport

DeformedMatrixComparison (2), (4) requires invertible charts on the exact
source and target of the prescribed matrix. Induction preserves the genuine
restriction-square isomorphism, and the selected append comparison supplies
the quotient chart. No invertibility premise on a comparison map is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {R S : Superfunctor k C (SVec k)}

/-- The induction of a given module isomorphism on literal coends. -/
def inducedMapIsoLinearEquiv (e : R ≅ S) (w : A) :
    Obj J R.toFunctor w ≃ₗ[k] Obj J S.toFunctor w :=
  moduleIsoLinearEquiv ((induction J).mapIso e) w

/-- For an even given isomorphism, its induced total map is its exact
parity-zero coend component. -/
theorem inducedMapIsoLinearEquiv_hom (e : R ≅ S)
    (he : e.hom ∈ parity (R := k) _ _ 0) (w : A) :
    (inducedMapIsoLinearEquiv J e w).toLinearMap = mapComponent J e.hom 0 w := by
  have hp := IsSuperfunctor.map_mem (F := induction J) he
  have hz := Superfunctor.app_eq_zero_of_mem hp (by decide : (1 : ZMod 2) ≠ 0) w
  change ((induction J).map e.hom).total w = _
  rw [SuperNatTrans.total, hz, add_zero]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The inverse canonical restriction comparison has degree zero. -/
theorem weightedAppendRestrictionIso_inv_mem :
    (weightedAppendRestrictionIso D Sc cutoff N i M).inv ∈ parity (R := k) _ _ 0 :=
  Supercategory.inv_mem (weightedAppendRestrictionIso D Sc cutoff N i M)
    (weightedAppendRestrictionIso_hom_mem D Sc cutoff N i M)

/-- The selected append isomorphism is a linear equivalence of the literal
old and truncated induction coends. -/
def weightedAppendLinearEquiv (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (RM).toFunctor w ≃ₗ[k]
      BalancedInduction.Obj T M.toFunctor ((Q).obj w) :=
  moduleIsoLinearEquiv (appendWeightedModuleIso D Sc cutoff N i M) ((Q).obj w)

/-- Its forward map is the selected comparison, including all five legs. -/
theorem weightedAppendLinearEquiv_hom (w : OldCategory D Sc cutoff) :
    (weightedAppendLinearEquiv D Sc cutoff N i M w).toLinearMap =
      weightedAppendComparisonLinear D Sc cutoff N i M w := rfl

/-- The given input isomorphism is induced before the selected quotient
comparison. The input module stays independent of any restriction. -/
def weightedAppendSourceLinearEquiv
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (e : R ≅ weightedRestriction D Sc cutoff N L) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J R.toFunctor w ≃ₗ[k]
      BalancedInduction.Obj T L.toFunctor ((Q).obj w) :=
  (BalancedInduction.inducedMapIsoLinearEquiv J e w).trans
    (weightedAppendLinearEquiv D Sc cutoff N i L w)

theorem weightedAppendSourceLinearEquiv_hom
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (e : R ≅ weightedRestriction D Sc cutoff N L)
    (he : e.hom ∈ parity (R := k) _ _ 0) (w : OldCategory D Sc cutoff) :
    (weightedAppendSourceLinearEquiv D Sc cutoff N i R L e w).toLinearMap =
      weightedAppendSourceLinear D Sc cutoff N i R L e.hom w := by
  unfold weightedAppendSourceLinearEquiv
  rw [LinearEquiv.coe_trans, BalancedInduction.inducedMapIsoLinearEquiv_hom J e he w,
    weightedAppendLinearEquiv_hom]
  rfl

/-- The source chart first induces the inverse restriction-square isomorphism,
then applies the selected quotient comparison on the restricted module. -/
abbrev weightedMateSourceLinearEquiv (w : OldCategory D Sc cutoff) :=
  weightedAppendSourceLinearEquiv D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
    ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).symm w

/-- The chart uses exactly the source map in the ordered mate comparison. -/
theorem weightedMateSourceLinearEquiv_hom (w : OldCategory D Sc cutoff) :
    (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap =
      weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
        ((BalancedInduction.restriction T).obj M)
        (weightedAppendRestrictionIso D Sc cutoff N i M).inv w :=
  weightedAppendSourceLinearEquiv_hom D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
    ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).symm
    (weightedAppendRestrictionIso_inv_mem D Sc cutoff N i M) w

/-- The target chart is the same selected append comparison at the appended
old output word, exactly as in the ordered mate comparison. -/
abbrev weightedMateTargetLinearEquiv (w : OldCategory D Sc cutoff) :=
  weightedAppendLinearEquiv D Sc cutoff N i M ((J).obj w)

theorem weightedMateTargetLinearEquiv_hom (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap =
      weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) := rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Dot transport by weighted append comparison

The generator compatibility in DeformedActionAssembly §§5–6 and STATUS
critical-chain item 2 uses
the selected five-isomorphism comparison. It intertwines the old signed
coend dot with the literal truncated appended dot, retaining the parity
twist of arbitrary old arrows.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The old dot maps to the same appended affine diagram in the literal
weighted quotient. -/
theorem oldTruncateFunctor_map_appendDot (s : OldCategory D Sc cutoff) :
    (Q).map (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i s) =
      truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0) ((Q).obj s) := rfl

/-- The chosen weighted append comparison intertwines the actual signed
old coend dot and the prescribed truncated dot on every output word.
No homogeneous-arrow or homogeneous-vector restriction is needed. -/
theorem appendWeightedModuleIso_hom_dot (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M w ∘ₗ
        CyclotomicCrossingTensor.inductionDot D Sc cutoff i RM w =
      BalancedInduction.transformLinear
        (truncatedAppendComponent_supernatural D Sc cutoff N (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M ((Q).obj w) ∘ₗ
        weightedAppendComparisonLinear D Sc cutoff N i M w := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply,
    CyclotomicCrossingTensor.inductionDot_tensor,
    appendWeightedModuleIso_hom_tensor, BalancedInduction.transformLinear_tensor]
  rw [(Q).map_comp, map_twist, oldTruncateFunctor_map_appendDot]
  rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Dotted rows under the weighted matrix charts

DeformedMatrixComparison (2), (4) uses the ordinary unit/dot columns and
dot/counit rows. The same prescribed module maps are evaluated on literal
coends before the selected weighted source and target charts are applied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

/-- The given homogeneous dot, with its module endomorphism endpoint fixed. -/
def dotEnd (M : Superfunctor k C (SVec k)) : End ((induction J).obj M) :=
  transformComponent hα M

theorem dotEnd_mem (M : Superfunctor k C (SVec k)) :
    dotEnd J hα M ∈ parity (R := k) _ _ p := by
  change transformComponent hα M ∈ parity (R := k) (induced J M) (induced J M) p
  exact transformComponent_mem hα M

/-- The actual ordinary unit followed by the restricted dot power. -/
def unitDotColumn (M : Superfunctor k C (SVec k)) (n : ℕ) :
    M ⟶ (restriction J).obj ((induction J).obj M) :=
  (adjunction J).unit.app M ≫ (restriction J).map ((dotEnd J hα M) ^ n)

/-- The actual dot power followed by the ordinary counit. -/
def capDotRow (N : Superfunctor k A (SVec k)) (n : ℕ) :
    (induction J).obj ((restriction J).obj N) ⟶ N :=
  ((dotEnd J hα ((restriction J).obj N)) ^ n) ≫ (adjunction J).counit.app N

theorem transform_power_mem (M : Superfunctor k C (SVec k)) (n : ℕ) :
    (dotEnd J hα M) ^ n ∈ parity (R := k) _ _ (n • p) := by
  induction n with
  | zero =>
    simp only [pow_zero, End.one_def, zero_nsmul]
    exact id_mem _
  | succ n ih =>
    rw [pow_succ, End.mul_def]
    simpa only [succ_nsmul, add_comm] using comp_mem (dotEnd_mem J hα M) ih

theorem unitDotColumn_mem (M : Superfunctor k C (SVec k)) (n : ℕ) :
    unitDotColumn J hα M n ∈ parity (R := k) _ _ (n • p) := by
  have h := comp_mem (adjunctionUnit_mem J M)
    (IsSuperfunctor.map_mem (F := restriction J) (transform_power_mem J hα M n))
  simpa only [unitDotColumn, zero_add] using h

theorem capDotRow_mem (N : Superfunctor k A (SVec k)) (n : ℕ) :
    capDotRow J hα N n ∈ parity (R := k) _ _ (n • p) := by
  simpa only [capDotRow, add_zero] using comp_mem
    (transform_power_mem J hα ((restriction J).obj N) n) (adjunctionCounit_mem J N)

private theorem total_power {F : Superfunctor k A (SVec k)} (f : End F) (w : A) (n : ℕ) :
    SVec.toLinearMap ((f ^ n).total w) = (SVec.toLinearMap (f.total w)) ^ n := by
  induction n with
  | zero =>
    change SVec.toLinearMap (SuperNatTrans.id F.toFunctor |>.total w) = LinearMap.id
    rw [SuperNatTrans.id_total, SVec.toLinearMap_id]
  | succ n ih =>
    rw [pow_succ, End.mul_def, Superfunctor.comp_total, SVec.toLinearMap_comp, ih, pow_succ]
    rfl

private theorem transform_total (M : Superfunctor k C (SVec k)) (w : A) :
    SVec.toLinearMap ((dotEnd J hα M).total w) = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [dotEnd, SuperNatTrans.total, transformComponent_app, ite_true, ite_false,
      zero_ne_one, one_ne_zero, zero_add, add_zero, SVec.toLinearMap]

private theorem transform_power_total (M : Superfunctor k C (SVec k)) (w : A) (n : ℕ) :
    SVec.toLinearMap (((dotEnd J hα M) ^ n).total w) = (transformLinear hα M w) ^ n := by
  have h := total_power (dotEnd J hα M) w n
  rw [transform_total] at h
  exact h

private theorem restriction_total {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction J).map f).total w = f.total (J.obj w) := rfl

private theorem unit_total (M : Superfunctor k C (SVec k)) (w : C) :
    SVec.toLinearMap (((adjunction J).unit.app M).total w) = unit J M.toFunctor w := by
  change SVec.toLinearMap (((adjunctionUnit J).app M).total w) = _
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ite_true, one_ne_zero, ite_false, add_zero, SVec.toLinearMap]

private theorem counit_total (N : Superfunctor k A (SVec k)) (w : A) :
    SVec.toLinearMap (((adjunction J).counit.app N).total w) = restrictionCounitLinear J N w := by
  change SVec.toLinearMap (((adjunctionCounit J).app N).total w) = _
  simp only [adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ite_true, one_ne_zero, ite_false, add_zero, SVec.toLinearMap]
  rfl

/-- Literal unit/dot component of the given ordinary module column. -/
def unitDotLinear (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    M.obj w →ₗ[k] Obj J M.toFunctor (J.obj w) :=
  ((transformLinear hα M (J.obj w)) ^ n) ∘ₗ unit J M.toFunctor w

/-- Literal dot/counit component of the given ordinary module row. -/
def capDotLinear (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    Obj J ((restriction J).obj N).toFunctor w →ₗ[k] N.obj w :=
  restrictionCounitLinear J N w ∘ₗ ((transformLinear hα ((restriction J).obj N) w) ^ n)

theorem unitDotColumn_total (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    SVec.toLinearMap ((unitDotColumn J hα M n).total w) = unitDotLinear J hα M n w := by
  rw [unitDotColumn, Superfunctor.comp_total, SVec.toLinearMap_comp,
    restriction_total, transform_power_total, unit_total]
  rfl

theorem capDotRow_total (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    SVec.toLinearMap ((capDotRow J hα N n).total w) = capDotLinear J hα N n w := by
  rw [capDotRow, Superfunctor.comp_total, SVec.toLinearMap_comp,
    transform_power_total, counit_total]
  rfl

private theorem twist_equality {w v : A} (e : w = v) :
    twist k p (eqToHom e) = eqToHom e := by
  cases e
  exact twist_id (R := k) p w

/-- The actual unit column at a canonically identified output object. -/
def endpointUnitDotLinear (M : Superfunctor k C (SVec k)) (n : ℕ)
    (w : C) (v : A) (e : J.obj w = v) : M.obj w →ₗ[k] Obj J M.toFunctor v :=
  ((transformLinear hα M v) ^ n) ∘ₗ (postcompose J M.toFunctor (eqToHom e) ∘ₗ unit J M.toFunctor w)

theorem endpointUnitDotLinear_total (M : Superfunctor k C (SVec k)) (n : ℕ)
    (w : C) (v : A) (e : J.obj w = v) :
    postcompose J M.toFunctor (eqToHom e) ∘ₗ
      SVec.toLinearMap ((unitDotColumn J hα M n).total w) = endpointUnitDotLinear J hα M n w v e := by
  rw [unitDotColumn_total]
  have hn := transformLinear_naturality hα M (eqToHom e)
  rw [twist_equality] at hn
  have hp := intertwine_pow (postcompose J M.toFunctor (eqToHom e))
    (transformLinear hα M (J.obj w)) (transformLinear hα M v) hn.symm n
  unfold unitDotLinear endpointUnitDotLinear
  rw [← LinearMap.comp_assoc, hp, LinearMap.comp_assoc]

private theorem inducedMapIsoLinearEquiv_symm_hom
    {R S : Superfunctor k C (SVec k)} (e : R ≅ S)
    (he : e.inv ∈ parity (R := k) _ _ 0) (w : A) :
    (inducedMapIsoLinearEquiv J e w).symm.toLinearMap = mapComponent J e.inv 0 w := by
  have hp := IsSuperfunctor.map_mem (F := induction J) he
  have hz := Superfunctor.app_eq_zero_of_mem hp (by decide : (1 : ZMod 2) ≠ 0) w
  change ((induction J).map e.inv).total w = _
  rw [SuperNatTrans.total, hz, add_zero]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u

private theorem compose_intertwine
    {k V W Z : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (C₁ : V →ₗ[k] W) (C₂ : W →ₗ[k] Z)
    (f : Module.End k V) (g : Module.End k W) (h : Module.End k Z)
    (h₁ : C₁ ∘ₗ f = g ∘ₗ C₁) (h₂ : C₂ ∘ₗ g = h ∘ₗ C₂) :
    (C₂ ∘ₗ C₁) ∘ₗ f = h ∘ₗ (C₂ ∘ₗ C₁) := by
  apply LinearMap.ext
  intro x
  exact (congrArg C₂ (LinearMap.congr_fun h₁ x)).trans (LinearMap.congr_fun h₂ (C₁ x))

private theorem counit_source_iso
    {k V W Z P : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    [AddCommMonoid P] [Module k P]
    (e : V ≃ₗ[k] W) (C : W →ₗ[k] Z) (r : V →ₗ[k] P) (s : Z →ₗ[k] P)
    (A : W →ₗ[k] V) (B : V →ₗ[k] W)
    (hA : A = e.symm.toLinearMap) (hB : B = e.toLinearMap)
    (hc : s ∘ₗ C = r ∘ₗ A) : s ∘ₗ (C ∘ₗ B) = r := by
  rw [hA] at hc
  rw [hB]
  apply LinearMap.ext
  intro x
  exact (LinearMap.congr_fun hc (e x)).trans (congrArg r (e.symm_apply_apply x))

private theorem unit_power_square
    {k V W P : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid P] [Module k P]
    (C : V →ₗ[k] W) (f : Module.End k V) (g : Module.End k W)
    (u : P →ₗ[k] V) (v : P →ₗ[k] W)
    (hd : C ∘ₗ f = g ∘ₗ C) (hu : C ∘ₗ u = v) (n : ℕ) :
    C ∘ₗ ((f ^ n) ∘ₗ u) = (g ^ n) ∘ₗ v := by
  apply LinearMap.ext
  intro x
  exact (intertwine_pow_apply C f g (fun y => LinearMap.congr_fun hd y) n (u x)).trans
    (congrArg (fun y => (g ^ n) y) (LinearMap.congr_fun hu x))

private theorem cap_power_square
    {k V W P : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid P] [Module k P]
    (C : V →ₗ[k] W) (f : Module.End k V) (g : Module.End k W)
    (r : V →ₗ[k] P) (s : W →ₗ[k] P)
    (hd : C ∘ₗ f = g ∘ₗ C) (hc : s ∘ₗ C = r) (n : ℕ) :
    (s ∘ₗ (g ^ n)) ∘ₗ C = r ∘ₗ (f ^ n) := by
  apply LinearMap.ext
  intro x
  exact (congrArg s
    (intertwine_pow_apply C f g (fun y => LinearMap.congr_fun hd y) n x).symm).trans
      (LinearMap.congr_fun hc ((f ^ n) x))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- The prescribed right-append dot in the literal truncated category. -/
theorem truncatedDot_supernatural : IsSupernatural k (D.parity i)
    (truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0)) :=
  truncatedAppendComponent_supernatural D Sc cutoff N (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The old column here is exactly the prescribed module-unit column. -/
theorem oldUnitColumn_eq (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    CyclotomicCrossingTensor.moduleUnitColumn D Sc cutoff i P n =
      BalancedInduction.unitDotColumn J (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) P n := rfl

/-- The old row here is exactly the prescribed module-cap row. -/
theorem oldCapRow_eq (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    CyclotomicCrossingTensor.moduleCapRow D Sc cutoff i P n =
      BalancedInduction.capDotRow J (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) P n := rfl

/-- The source comparison intertwines the given signed dot on every input
module map's parity-zero component, before restriction is specialized. -/
theorem weightedAppendSourceLinear_dot
    (R : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (c : R ⟶ weightedRestriction D Sc cutoff N L) (w : OldCategory D Sc cutoff) :
    weightedAppendSourceLinear D Sc cutoff N i R L c w ∘ₗ
        BalancedInduction.transformLinear
          (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) R w =
      BalancedInduction.transformLinear (truncatedDot_supernatural D Sc cutoff N i) L ((Q).obj w) ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i R L c w := by
  have h₁ := BalancedInduction.transform_mapComponent
    (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) R c 0 w
  have h₁' : BalancedInduction.mapComponent J c 0 w ∘ₗ
      BalancedInduction.transformLinear
          (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) R w =
      BalancedInduction.transformLinear
        (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i)
        (weightedRestriction D Sc cutoff N L) w ∘ₗ BalancedInduction.mapComponent J c 0 w := by
    simpa only [mul_zero, sign_zero, one_smul] using h₁.symm
  exact compose_intertwine (BalancedInduction.mapComponent J c 0 w)
    (weightedAppendComparisonLinear D Sc cutoff N i L w)
    (BalancedInduction.transformLinear
          (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) R w)
    (BalancedInduction.transformLinear
      (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) (weightedRestriction D Sc cutoff N L) w)
    (BalancedInduction.transformLinear (truncatedDot_supernatural D Sc cutoff N i) L ((Q).obj w)) h₁'
    (by simpa only [CyclotomicCrossingTensor.inductionDot] using
      appendWeightedModuleIso_hom_dot D Sc cutoff N i L w)

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The exact source chart of the mate comparison also transports the
ordinary counit, using the induced genuine restriction isomorphism. -/
theorem weightedMateSourceLinear_counit (w : OldCategory D Sc cutoff) :
    restrictionCounitLinear T M ((Q).obj w) ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
          ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).inv w =
      restrictionCounitLinear J RM w := by
  exact counit_source_iso
    (BalancedInduction.inducedMapIsoLinearEquiv J (weightedAppendRestrictionIso D Sc cutoff N i M).symm w)
    (weightedAppendComparisonLinear D Sc cutoff N i ((BalancedInduction.restriction T).obj M) w)
    (restrictionCounitLinear J RM w) (restrictionCounitLinear T M ((Q).obj w))
    (BalancedInduction.mapComponent J (weightedAppendRestrictionIso D Sc cutoff N i M).hom 0 w)
    (BalancedInduction.mapComponent J (weightedAppendRestrictionIso D Sc cutoff N i M).inv 0 w)
    (BalancedInduction.inducedMapIsoLinearEquiv_symm_hom J
      (weightedAppendRestrictionIso D Sc cutoff N i M).symm
      (weightedAppendRestrictionIso_hom_mem D Sc cutoff N i M) w).symm
    (BalancedInduction.inducedMapIsoLinearEquiv_hom J
      (weightedAppendRestrictionIso D Sc cutoff N i M).symm
      (weightedAppendRestrictionIso_inv_mem D Sc cutoff N i M) w).symm
    (appendWeightedModuleIso_hom_counit D Sc cutoff N i M w)

/-- The target chart transports the ordinary unit with its canonical output
object identity retained explicitly. -/
theorem weightedMateTargetLinear_unit (w : OldCategory D Sc cutoff) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        BalancedInduction.unit J (RM).toFunctor w =
      BalancedInduction.postcompose T M.toFunctor
        (eqToHom (show (T).obj ((Q).obj w) = (Q).obj ((J).obj w) from rfl)) ∘ₗ
          BalancedInduction.unit T M.toFunctor ((Q).obj w) := by
  apply LinearMap.ext
  intro b
  have hu := appendWeightedModuleIso_hom_unit D Sc cutoff N i M w b
  have hp : BalancedInduction.postcompose T M.toFunctor
      (eqToHom (show (T).obj ((Q).obj w) = (Q).obj ((J).obj w) from rfl))
        (BalancedInduction.unit T M.toFunctor ((Q).obj w) b) =
      BalancedInduction.unit T M.toFunctor ((Q).obj w) b := by
    change BalancedInduction.postcompose T M.toFunctor (𝟙 ((Q).obj ((J).obj w))) _ = _
    exact LinearMap.congr_fun (BalancedInduction.postcompose_id T M.toFunctor ((Q).obj ((J).obj w))) _
  exact hu.trans hp.symm

/-- Every prescribed unscaled unit/dot column commutes with the selected
target chart, including either moving parity and arbitrary dot powers. -/
theorem weightedMateTargetLinear_unitDot (w : OldCategory D Sc cutoff) (n : ℕ) :
    weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w) ∘ₗ
        BalancedInduction.unitDotLinear J
          (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) RM n w =
      BalancedInduction.endpointUnitDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n
        ((Q).obj w) ((Q).obj ((J).obj w)) rfl := by
  have h := unit_power_square
    (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w))
    (BalancedInduction.transformLinear
      (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) RM ((J).obj w))
    (BalancedInduction.transformLinear (truncatedDot_supernatural D Sc cutoff N i) M ((Q).obj ((J).obj w)))
    (BalancedInduction.unit J (RM).toFunctor w)
    (BalancedInduction.postcompose T M.toFunctor
      (eqToHom (show (T).obj ((Q).obj w) = (Q).obj ((J).obj w) from rfl)) ∘ₗ
        BalancedInduction.unit T M.toFunctor ((Q).obj w))
    (by simpa only [CyclotomicCrossingTensor.inductionDot] using
      appendWeightedModuleIso_hom_dot D Sc cutoff N i M ((J).obj w))
    (weightedMateTargetLinear_unit D Sc cutoff N i M w) n
  exact h

/-- Every prescribed unscaled dot/counit row commutes with the selected
source chart, with no row-normalization or comparison premise. -/
theorem weightedMateSourceLinear_capDot (w : OldCategory D Sc cutoff) (n : ℕ) :
    BalancedInduction.capDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w) ∘ₗ
        weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
          ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).inv w =
      BalancedInduction.capDotLinear J (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) RM n w := by
  exact cap_power_square
    (weightedAppendSourceLinear D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
      ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).inv w)
    (BalancedInduction.transformLinear (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i)
      ((BalancedInduction.restriction J).obj RM) w)
    (BalancedInduction.transformLinear (truncatedDot_supernatural D Sc cutoff N i)
      ((BalancedInduction.restriction T).obj M) ((Q).obj w))
    (restrictionCounitLinear J RM w) (restrictionCounitLinear T M ((Q).obj w))
    (weightedAppendSourceLinear_dot D Sc cutoff N i ((BalancedInduction.restriction J).obj RM)
      ((BalancedInduction.restriction T).obj M) (weightedAppendRestrictionIso D Sc cutoff N i M).inv w)
    (weightedMateSourceLinear_counit D Sc cutoff N i M w) n

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Iterated weighted append comparison

DeformedActionAssembly §5 and DeformedMatrixComparison (2), (4) use the
crossing on iterated induction. The comparison is obtained from the chosen
pair comparison by descending the old induction flattening and undoing the
truncated flattening. Thus its flattening coherence uses the prescribed maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

variable (i j : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "K" => CyclotomicCrossingTensor.append D Sc cutoff j
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "U" => truncatedAppend D Sc cutoff N [j]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "FI" => Functor.obj (BalancedInduction.induction J ⋙ BalancedInduction.induction K) RM
local notation "FP" => BalancedInduction.induced (J ⋙ K) RM
local notation "hFP" => pairInduced_killsWeightedCoefficients D Sc cutoff N i j RM
  (weightedRestriction_kills D Sc cutoff N M)

/-- The twice-induced old module satisfies the complete weighted annihilator. -/
theorem doubleInduced_killsWeightedCoefficients :
    KillsWeightedCoefficients D Sc cutoff N FI :=
  induced_killsWeightedCoefficients D Sc cutoff N j _
    (induced_killsWeightedCoefficients D Sc cutoff N i RM
      (weightedRestriction_kills D Sc cutoff N M))
local notation "hFI" => doubleInduced_killsWeightedCoefficients D Sc cutoff N i j M

end OddMath.QuiverHecke.ELVOld
end

end
