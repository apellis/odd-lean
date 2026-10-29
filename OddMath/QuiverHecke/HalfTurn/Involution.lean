/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.HalfTurn.CornerIdeal

/-!
# The half-turn is an involution on coefficient-extended Hom spaces

`docs/Nondegeneracy/SwappedVacuumCoordinates.md` §4, last paragraph: the inverse of the half-turn
`U` uses the same generator table with `Sc` and `parameterTwist D Sc` interchanged. Reversal squares
to the identity, each weight `ε_ij` occurs twice, the signed reversed-product signs occur twice,
and coefficients are fixed; with `parameterTwist_involutive` both composites are the identity.

## Main declarations

* `scalarsCast`: the identification of coefficient-extended Hom spaces along equalities of the
  parameters and of the words.
* `halfTurnC_halfTurnL`: the scalar of a half-turned diagram does not change when the diagram
  is half-turned again.
* `htCoef_htCoef`: **`U' ∘ U = id`**, where `U'` is the half-turn for `parameterTwist D Sc`,
  up to `parameterTwist_involutive` and `s.reverse.reverse = s`.
* `htCoef_bijective`, `htCoefEquiv`: the half-turn is a linear isomorphism
  `Hom(s, t) ≅ Hom'(t^rev, s^rev)` of coefficient-extended Hom spaces.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
open SKM (zsign)
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-! ## Transport along equal parameters and words -/

/-- Coefficient-extended Hom spaces along equalities of the parameters and of the words. -/
def scalarsCast {Sc₁ Sc₂ : SKM.Scalars D k} (e : Sc₁ = Sc₂) {s s' t t' : List I} (hs : s = s')
    (ht : t = t') :
    (coefficientObj D Sc₁ s ⟶ coefficientObj D Sc₁ t) ≃ₗ[k]
      (coefficientObj D Sc₂ s' ⟶ coefficientObj D Sc₂ t') := by
  subst e hs ht; exact LinearEquiv.refl k _

theorem scalarsCast_refl {s t : List I} (x : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    scalarsCast D (rfl : Sc = Sc) (rfl : s = s) (rfl : t = t) x = x := rfl

theorem scalarsCast_scalarsCast {Sc₁ Sc₂ Sc₃ : SKM.Scalars D k} (e : Sc₁ = Sc₂) (e' : Sc₂ = Sc₃)
    {s s' s'' t t' t'' : List I} (hs : s = s') (ht : t = t') (hs' : s' = s'') (ht' : t' = t'')
    (x : coefficientObj D Sc₁ s ⟶ coefficientObj D Sc₁ t) :
    scalarsCast D e' hs' ht' (scalarsCast D e hs ht x) =
      scalarsCast D (e.trans e') (hs.trans hs') (ht.trans ht') x := by
  subst e e' hs ht hs' ht'; rfl

theorem scalarsCast_injective {Sc₁ Sc₂ : SKM.Scalars D k} (e : Sc₁ = Sc₂) {s s' t t' : List I}
    (hs : s = s') (ht : t = t') : Function.Injective (scalarsCast D e hs ht) :=
  (scalarsCast D e hs ht).injective

/-- A pure coefficient tensor of a normal-form diagram is transported to the same tensor. -/
theorem scalarsCast_sourceCoefficientHom_diag {Sc₁ Sc₂ : SKM.Scalars D k} (e : Sc₁ = Sc₂)
    {s s' t t' : List I} (hs : s = s') (ht : t = t') (a : SKM.SYM D k) (ls : List (LayerData I))
    (h : SChain s ls t) (h' : SChain s' ls t') :
    scalarsCast D e hs ht (sourceCoefficientHom D Sc₁ a ((pres D Sc₁).diag (mkD D ls h))) =
      sourceCoefficientHom D Sc₂ a ((pres D Sc₂).diag (mkD D ls h')) := by
  subst e hs ht; rfl

/-- The half-turn commutes with the transport along equal parameters and words. -/
theorem htCoef_scalarsCast {Sc₁ Sc₂ : SKM.Scalars D k} (e : Sc₁ = Sc₂) {s s' t t' : List I}
    (hs : s = s') (ht : t = t') (x : coefficientObj D Sc₁ s ⟶ coefficientObj D Sc₁ t) :
    htCoef D Sc₂ s' t' (scalarsCast D e hs ht x) =
      scalarsCast D (congrArg (parameterTwist D) e) (congrArg List.reverse ht)
        (congrArg List.reverse hs) (htCoef D Sc₁ s t x) := by
  subst e hs ht; rfl

/-! ## The scalar of a twice half-turned diagram -/

/-- Half-turning a diagram twice gives the scalar `halfTurnC` twice. -/
theorem halfTurnC_halfTurnL (ls : List (LayerData I)) :
    halfTurnC (k := k) D (halfTurnL ls) = halfTurnC D ls := by
  induction ls with
  | nil => rfl
  | cons x ls ih =>
    have e : halfTurnL (x :: ls) = halfTurnL ls ++ [halfTurnLD x] := by simp [halfTurnL]
    rw [e, halfTurnC_append, ih, halfTurnC_singleton, halfTurnC_cons, psum_halfTurnL]
    have hx : psum D [halfTurnLD x] = x.2.1.parity D := by simp [psum, halfTurnLD]
    have hw : (halfTurnLD x).2.1 = x.2.1 := rfl
    rw [hx, hw, mul_comm (psum D ls)]
    ring

/-! ## The half-turn is an involution -/

set_option backward.isDefEq.respectTransparency false in
/-- **The half-turn is an involution**: the half-turn for `parameterTwist D Sc` after the
half-turn for `Sc` is the identity, transported along `parameterTwist_involutive` and
`s.reverse.reverse = s` (`SwappedVacuumCoordinates.md` §4). -/
theorem htCoef_htCoef {s t : List I} (x : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    htCoef D (parameterTwist D Sc) t.reverse s.reverse (htCoef D Sc s t x) =
      scalarsCast D (parameterTwist_involutive D Sc).symm (List.reverse_reverse s).symm
        (List.reverse_reverse t).symm x := by
  refine coef_induction D Sc (P := fun x => htCoef D (parameterTwist D Sc) t.reverse s.reverse
    (htCoef D Sc s t x) = scalarsCast D (parameterTwist_involutive D Sc).symm
      (List.reverse_reverse s).symm (List.reverse_reverse t).symm x) ?_ ?_ ?_ x
  · simp
  · intro x y hx hy; simp only [map_add, hx, hy]
  intro _ a _ ls hl
  have hl' : SChain s.reverse.reverse ls t.reverse.reverse := by
    simpa only [List.reverse_reverse] using hl
  rw [htCoef_sourceCoefficientHom, htPres_diag_mkD, sourceCoefficientHom_smul_right, map_smul,
    htCoef_sourceCoefficientHom, htPres_diag_mkD, sourceCoefficientHom_smul_right, smul_smul,
    halfTurnC_halfTurnL, halfTurnC_mul_self, one_smul,
    scalarsCast_sourceCoefficientHom_diag D _ _ _ a ls hl hl']
  congr 1
  apply Presentation.diag_eq_of_layers_eq
  simp only [layers_mkD, halfTurnL_halfTurnL]

theorem htCoef_injective (s t : List I) : Function.Injective (htCoef D Sc s t) := by
  intro x y hxy
  have h := congrArg (htCoef D (parameterTwist D Sc) t.reverse s.reverse) hxy
  rw [htCoef_htCoef, htCoef_htCoef] at h
  exact scalarsCast_injective D _ _ _ h

/-- The preimage of `y` under the half-turn: the half-turn for `parameterTwist D Sc`,
transported back to `Sc` and to the words `s`, `t`. -/
def htCoefInv (s t : List I) :
    (coefficientObj D (parameterTwist D Sc) t.reverse ⟶
        coefficientObj D (parameterTwist D Sc) s.reverse) →ₗ[k]
      (coefficientObj D Sc s ⟶ coefficientObj D Sc t) :=
  (scalarsCast D (parameterTwist_involutive D Sc) (List.reverse_reverse s)
      (List.reverse_reverse t)).toLinearMap ∘ₗ htCoef D (parameterTwist D Sc) t.reverse s.reverse

theorem htCoefInv_htCoef {s t : List I} (x : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    htCoefInv D Sc s t (htCoef D Sc s t x) = x := by
  simp only [htCoefInv, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    htCoef_htCoef, scalarsCast_scalarsCast]
  rfl

theorem htCoef_htCoefInv {s t : List I}
    (y : coefficientObj D (parameterTwist D Sc) t.reverse ⟶
      coefficientObj D (parameterTwist D Sc) s.reverse) :
    htCoef D Sc s t (htCoefInv D Sc s t y) = y := by
  simp only [htCoefInv, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    htCoef_scalarsCast, htCoef_htCoef, scalarsCast_scalarsCast]
  rfl

theorem htCoef_surjective (s t : List I) : Function.Surjective (htCoef D Sc s t) :=
  fun y => ⟨htCoefInv D Sc s t y, htCoef_htCoefInv D Sc y⟩

/-- **The half-turn is bijective** on coefficient-extended Hom spaces. -/
theorem htCoef_bijective (s t : List I) : Function.Bijective (htCoef D Sc s t) :=
  ⟨htCoef_injective D Sc s t, htCoef_surjective D Sc s t⟩

/-- The half-turn as a linear isomorphism `Hom(s, t) ≅ Hom'(t^rev, s^rev)` of
coefficient-extended Hom spaces, `Hom'` for the parameters `parameterTwist D Sc`. -/
def htCoefEquiv (s t : List I) :
    (coefficientObj D Sc s ⟶ coefficientObj D Sc t) ≃ₗ[k]
      (coefficientObj D (parameterTwist D Sc) t.reverse ⟶
        coefficientObj D (parameterTwist D Sc) s.reverse) :=
  LinearEquiv.ofLinearMap (htCoef D Sc s t) (htCoefInv D Sc s t)
    (LinearMap.ext fun y => htCoef_htCoefInv D Sc y)
    (LinearMap.ext fun x => htCoefInv_htCoef D Sc x)

@[simp] theorem htCoefEquiv_apply {s t : List I}
    (x : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    htCoefEquiv D Sc s t x = htCoef D Sc s t x := rfl

@[simp] theorem htCoefEquiv_symm_apply {s t : List I}
    (y : coefficientObj D (parameterTwist D Sc) t.reverse ⟶
      coefficientObj D (parameterTwist D Sc) s.reverse) :
    (htCoefEquiv D Sc s t).symm y = htCoefInv D Sc s t y := rfl

end OddMath.QuiverHecke
