/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HalfTurn.Composite
import OddMath.QuiverHecke.SwappedVacuum.TransformedIdeal

/-!
# The half-turn on coefficient-extended Hom spaces and the transformed ideal

`docs/Nondegeneracy/SwappedVacuumCoordinates.md` §§4–5. The half-turn `U` (`halfTurnFunctor`)
gives linear maps `htPres` on the Hom spaces of the quiver Hecke supercategory, reversing words
and the direction of morphisms, and `htCoef` on the coefficient-extended Hom spaces, by
`U(a ⊗ f) = a ⊗ U(f)`, with no coefficient sign.

## Main declarations

* `htPres`, `htPres_diag_mkD`: the half-turn on Hom spaces and its value on a normal-form
  diagram.
* `htPres_diag_comp`: the signed reversal of composition, `U(f ≫ g) = (-1)^{|f||g|} U(g) ≫ U(f)`,
  for normal-form diagrams.
* `htCoef`, `htCoef_coefficientHom`: the half-turn on coefficient-extended Hom spaces.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open SKM (zsign)
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-! ## Combinatorics of the reflected layers -/

theorem halfTurnL_append (A B : List (LayerData I)) :
    halfTurnL (A ++ B) = halfTurnL B ++ halfTurnL A := by
  simp [halfTurnL]

theorem halfTurnLD_halfTurnLD (x : LayerData I) : halfTurnLD (halfTurnLD x) = x := by
  obtain ⟨u, g, v⟩ := x
  simp [halfTurnLD]

theorem halfTurnL_halfTurnL (ls : List (LayerData I)) : halfTurnL (halfTurnL ls) = ls := by
  simp [halfTurnL, List.map_reverse, Function.comp_def, halfTurnLD_halfTurnLD]

theorem psum_halfTurnL (ls : List (LayerData I)) : psum D (halfTurnL ls) = psum D ls := by
  induction ls with
  | nil => rfl
  | cons x ls ih =>
    simp only [halfTurnL] at ih ⊢
    rw [List.map_cons, List.reverse_cons, psum_append, ih, psum_cons, add_comm]
    simp [psum, halfTurnLD]

theorem halfTurnC_append (A B : List (LayerData I)) :
    halfTurnC (k := k) D (A ++ B) =
      zsign k (psum D A * psum D B) * halfTurnC D A * halfTurnC D B := by
  induction A with
  | nil => simp [SKM.zsign]
  | cons x A ih =>
    simp only [List.cons_append, halfTurnC_cons, ih, psum_append, psum_cons, mul_add, add_mul,
      SKM.zsign_add]
    ring

theorem halfTurnWeight_mul_self (g : Shape I) : halfTurnWeight (k := k) g * halfTurnWeight g = 1 := by
  cases g with
  | dot i => simp [halfTurnWeight]
  | cross i j => by_cases h : i = j <;> simp [halfTurnWeight, h]

theorem halfTurnC_mul_self (ls : List (LayerData I)) :
    halfTurnC (k := k) D ls * halfTurnC D ls = 1 := by
  induction ls with
  | nil => simp
  | cons x ls ih =>
    rw [halfTurnC_cons]
    calc _ = (zsign k (x.2.1.parity D * psum D ls) * zsign k (x.2.1.parity D * psum D ls)) *
          (halfTurnWeight x.2.1 * halfTurnWeight x.2.1) * (halfTurnC D ls * halfTurnC D ls) := by
          ring
      _ = 1 := by rw [zsign_mul_self, halfTurnWeight_mul_self, ih, one_mul, one_mul]

/-! ## The half-turn on Hom spaces -/

instance halfTurnFunctor_additive : (halfTurnFunctor D Sc).Additive := by
  unfold halfTurnFunctor mirrorFunctor flipFunctor; infer_instance

instance halfTurnFunctor_linear : (halfTurnFunctor D Sc).Linear k := by
  unfold halfTurnFunctor mirrorFunctor flipFunctor; infer_instance

/-- The half-turn on Hom spaces, `Hom(s, t) → Hom(t^rev, s^rev)`. -/
def htPres (s t : List I) :
    ((pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) →ₗ[k]
      ((pres D (parameterTwist D Sc)).obj (ob D t.reverse) ⟶
        (pres D (parameterTwist D Sc)).obj (ob D s.reverse)) :=
  ((pres D (parameterTwist D Sc)).castLinearEquiv (halfTurn_obj D t)
      (halfTurn_obj D s)).toLinearMap ∘ₗ
    SOp.unsopₗ _ _ ∘ₗ (halfTurnFunctor D Sc).mapLinearMap k

theorem htPres_apply {s t : List I} (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    htPres D Sc s t f = (pres D (parameterTwist D Sc)).castLinearEquiv (halfTurn_obj D t)
      (halfTurn_obj D s) (SOp.unsop ((halfTurnFunctor D Sc).map f)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The half-turn of a normal-form diagram: the reflected layers in reverse order, times
`halfTurnC`. -/
theorem htPres_diag_mkD {s t : List I} (ls : List (LayerData I)) (h : SChain s ls t) :
    htPres D Sc s t ((pres D Sc).diag (mkD D ls h)) =
      halfTurnC (k := k) D ls •
        (pres D (parameterTwist D Sc)).diag (mkD D (halfTurnL ls) (sChain_halfTurnL h)) := by
  rw [htPres_apply, halfTurn_mkD, map_smul, Presentation.castLinearEquiv_apply,
    Presentation.castHom_diag, Diagram.cast_cast]
  refine congrArg (halfTurnC (k := k) D ls • ·) ?_
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_cast]

theorem diag_mkD_mem_parity {s t : List I} (ls : List (LayerData I)) (h : SChain s ls t) :
    (pres D Sc).diag (mkD D ls h) ∈ Supercategory.parity (R := k) _ _ (psum D ls) :=
  Presentation.diag_mem_homDeg' (degree_parity_mkD D _ _)

theorem htPres_diag_mkD_mem_parity {s t : List I} (ls : List (LayerData I)) (h : SChain s ls t) :
    htPres D Sc s t ((pres D Sc).diag (mkD D ls h)) ∈
      Supercategory.parity (R := k) _ _ (psum D ls) := by
  rw [htPres_diag_mkD, ← psum_halfTurnL D ls]
  exact Submodule.smul_mem _ _ (diag_mkD_mem_parity D _ _ _)

/-- **The signed reversal of composition** for normal-form diagrams:
`U(f ≫ g) = (-1)^{|f||g|} U(g) ≫ U(f)`. -/
theorem htPres_diag_comp {s t r : List I} (A B : List (LayerData I)) (hA : SChain s A t)
    (hB : SChain t B r) :
    htPres D Sc s r ((pres D Sc).diag (mkD D A hA) ≫ (pres D Sc).diag (mkD D B hB)) =
      zsign k (psum D A * psum D B) •
        (htPres D Sc t r ((pres D Sc).diag (mkD D B hB)) ≫
          htPres D Sc s t ((pres D Sc).diag (mkD D A hA))) := by
  rw [← diag_mkD_append D Sc A B (hA.append hB) hA hB, htPres_diag_mkD, htPres_diag_mkD,
    htPres_diag_mkD, Linear.smul_comp, Linear.comp_smul, ← diag_mkD_append D (parameterTwist D Sc)
      (halfTurnL B) (halfTurnL A) ((sChain_halfTurnL hB).append (sChain_halfTurnL hA)),
    smul_smul, smul_smul, halfTurnC_append]
  have e : (pres D (parameterTwist D Sc)).diag (mkD D (halfTurnL (A ++ B))
      (sChain_halfTurnL (hA.append hB))) = (pres D (parameterTwist D Sc)).diag
      (mkD D (halfTurnL B ++ halfTurnL A)
        ((sChain_halfTurnL hB).append (sChain_halfTurnL hA))) :=
    Presentation.diag_eq_of_layers_eq _ (by simp only [layers_mkD, halfTurnL_append])
  rw [e]
  congr 1
  ring

theorem htPres_id (t : List I) :
    htPres D Sc t t (𝟙 _) = 𝟙 _ := by
  have e : (𝟙 ((pres D Sc).obj (ob D t))) = (pres D Sc).diag (mkD D [] (t := t) (t' := t) rfl) := by
    rw [← Presentation.diag_id]; rfl
  rw [e, htPres_diag_mkD, halfTurnC_nil, one_smul, ← Presentation.diag_id]
  rfl

/-! ## The half-turn on coefficient-extended Hom spaces -/

/-- The half-turn on coefficient-extended Hom spaces: `a ⊗ f ↦ a ⊗ U(f)`. -/
def htCoef (s t : List I) :
    (coefficientObj D Sc s ⟶ coefficientObj D Sc t) →ₗ[k]
      (coefficientObj D (parameterTwist D Sc) t.reverse ⟶
        coefficientObj D (parameterTwist D Sc) s.reverse) :=
  (sourceTensorEquiv D (parameterTwist D Sc) t.reverse s.reverse).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (htPres D Sc s t) ∘ₗ
      (sourceTensorEquiv D Sc s t).symm.toLinearMap

/-- `U(a ⊗ f) = a ⊗ U(f)`, with no coefficient sign (§4). -/
@[simp] theorem htCoef_sourceCoefficientHom {s t : List I} (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)) :
    htCoef D Sc s t (sourceCoefficientHom D Sc a f) =
      sourceCoefficientHom D (parameterTwist D Sc) a (htPres D Sc s t f) := by
  rw [show sourceCoefficientHom D Sc a f = sourceTensorEquiv D Sc s t (a ⊗ₜ[k] f) from rfl]
  rw [htCoef, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rfl

/-- Composition of three pure coefficient tensors. -/
theorem sourceCoefficientHom_comp_comp {s v w t : List I} {p q r₁ r₂ : ZMod 2}
    {α γ : SKM.SYM D k} (β : SKM.SYM D k)
    (hα : SKM.SYM.polynomialExteriorEquiv D k α ∈ SKM.SYM.polynomialExteriorParity D k p)
    (hγ : SKM.SYM.polynomialExteriorEquiv D k γ ∈ SKM.SYM.polynomialExteriorParity D k q)
    (f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D v))
    {g : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    {h : (pres D Sc).obj (ob D w) ⟶ (pres D Sc).obj (ob D t)}
    (hg : g ∈ Supercategory.parity (R := k) _ _ r₁)
    (hh : h ∈ Supercategory.parity (R := k) _ _ r₂) :
    sourceCoefficientHom D Sc α f ≫ sourceCoefficientHom D Sc γ g ≫ sourceCoefficientHom D Sc β h =
      ((koszulSign q r₂ * koszulSign p (r₁ + r₂) : ℤ) : k) •
        sourceCoefficientHom D Sc (β * γ * α) (f ≫ g ≫ h) := by
  rw [sourceCoefficientHom_comp D Sc hγ _ _ hh, Preadditive.comp_zsmul,
    sourceCoefficientHom_comp D Sc hα _ _ (Supercategory.comp_mem hg hh), smul_smul,
    ← Int.cast_smul_eq_zsmul k, Int.cast_mul, mul_comm (koszulSign q r₂ : k)]

end OddMath.QuiverHecke
