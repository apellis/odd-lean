/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.ModifiedBaseChange
import OddMath.CoveringQuantum.UDot.Twistor
import OddMath.CoveringQuantum.UDot.SesquilinearForm
import OddMath.CoveringQuantum.Coefficients.FormSplitting
import OddMath.CoveringQuantum.SerreBaseChange
import OddMath.CoveringQuantum.PreF.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Nondegeneracy of the form on `U̇` from the `π = 1` input

This file reduces the nondegeneracy statement of Brundan–Ellis, arXiv:1701.04133v2,
Theorem 10.1, for the `ρ`-adjoint form `GenericTensor.positiveModifiedForm` on the modified
covering algebra over `ℚ(q)[π]/(π² - 1)` (finite bar-consistent data, linearly independent simple
roots), to the corresponding statement for the modified quantum group at `π = 1` over a field.

The `π = 1` input is the Prop `PositiveFormNondegenerate D L q' 1`: every left `ρ`-adjoint
bilinear form on `U̇_{q',1}` over the field `L` with the standard values
`(E_a 1_μ, E_b 1_ν) = δ_{μν} (θ_a, θ_b)` on positive words has trivial left radical. It is **not
proved here**: it is an explicit hypothesis of the results below, to be discharged from Lusztig's
form on `U̇` ([Lus] 26.3.1).

The reduction:
* the covering ring splits through the specializations `π ↦ ±1` to `K = ℚ(q)`
  (`Coefficients.leftRadical_trivial_of_specialize`); each specialization is flat, so the
  specialized form is `baseChangeForm` along `modifiedBaseChange`;
* trivial left radical descends from a field extension `L / K`
  (`leftRadical_trivial_of_baseChangeForm`);
  over `L` the extended form is `ρ`-adjoint with the standard values on positive words;
* at `π = -1` the twistor `U̇_{q,-1} ≅ U̇_{tq,1}` (`t² = -1`) transports the question to `π = 1`
  (`positiveFormNondegenerate_neg_one_of_twist`).

## Main definitions

* `UDot.PositiveFormNondegenerate`: the nondegeneracy input over a field.
* `UDot.twistorModified`: the twistor restricted to the modified algebras.

## Main results

* `UDot.positiveFormNondegenerate_neg_one_of_twist`.
* `UDot.positiveModifiedForm_leftRadical_trivial`,
  `UDot.positiveModifiedForm_leftRadical_trivial_algebraicClosure`,
  `UDot.sesquilinearForm_leftRadical_trivial`.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

open TensorProduct PreF

variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] (D : RootDatum I X)

/-- The nondegeneracy input over a field `L`: every bilinear form on the modified algebra
`U̇_{q',π'}` which is left `ρ`-adjoint and takes the standard values
`(E_a 1_μ, E_b 1_ν) = δ_{μν} (θ_a, θ_b)` on positive words has trivial left radical. For `π' = 1`
this is to be supplied from Lusztig's form ([Lus] 26.3.1). -/
def PositiveFormNondegenerate (L : Type*) [Field L] (q' : Lˣ) (π' : L) (hπ' : π' ^ 2 = 1) :
    Prop :=
  ∀ B : LinearMap.BilinForm L (modified D q' π'),
    (∀ u x y, B (u * x) y = B x (rhoModified D q' π' hπ' u * y)) →
    (∀ a b μ ν, B (positiveWord D q' π' a μ) (positiveWord D q' π' b ν) =
      if μ = ν then D.form q' π' (monomial L a) (monomial L b) else 0) →
    ∀ x, (∀ y, B x y = 0) → x = 0

/-! ### The twistor step `π = 1 → π = -1` -/

section Twistor

variable [LinearOrder I] {β : X → I →₀ ℤ} (hβ : ∀ μ j, β (μ + D.α j) = β μ + Finsupp.single j 1)
variable {L : Type*} [Field L] {t : Lˣ} (ht : t ^ 2 = -1) (q : Lˣ) (hC : D.BarConsistent)

/-- The twistor `U̇_{q,-1} ≅ U̇_{tq,1}` restricted to the modified algebras. -/
def twistorModified : modified D q (-1) ≃ₗ[L] modified D (t * q) 1 where
  toFun x := ⟨twistor D hβ ht q hC x, twistor_mem_modified D hβ ht q hC x.property⟩
  invFun y := ⟨(twistor D hβ ht q hC).symm y, by
    unfold twistor
    rw [gaugeEquiv_symm_apply]
    exact gauge_mem_modified _ y.property⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul _ c x.1)
  left_inv x := Subtype.ext ((twistor D hβ ht q hC).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((twistor D hβ ht q hC).apply_symm_apply y.1)

@[simp] theorem coe_twistorModified (x : modified D q (-1)) :
    (twistorModified D hβ ht q hC x : CoveringUDot L D (t * q) 1) = twistor D hβ ht q hC x := rfl

@[simp] theorem coe_twistorModified_symm (y : modified D (t * q) 1) :
    ((twistorModified D hβ ht q hC).symm y : CoveringUDot L D q (-1)) =
      (twistor D hβ ht q hC).symm y := rfl

theorem twistorModified_symm_rhoModified (u : modified D (t * q) 1) :
    (twistorModified D hβ ht q hC).symm (rhoModified D (t * q) 1 (one_pow 2) u) =
      rhoModified D q (-1) neg_one_sq ((twistorModified D hβ ht q hC).symm u) := by
  apply Subtype.ext
  simp only [coe_twistorModified_symm, coe_rhoModified]
  rw [AlgEquiv.symm_apply_eq]
  have h := rho_twistor D hβ ht q hC ((twistor D hβ ht q hC).symm u)
  rw [AlgEquiv.apply_symm_apply, twistorAdjoint_eq] at h
  exact h

theorem twistorModified_symm_mul (u v : modified D (t * q) 1) :
    (twistorModified D hβ ht q hC).symm (u * v) =
      (twistorModified D hβ ht q hC).symm u * (twistorModified D hβ ht q hC).symm v :=
  Subtype.ext (map_mul (twistor D hβ ht q hC).symm u.1 v.1)

omit [DecidableEq I] [DecidableEq X] in
/-- The twistor phases of positive words are signs. -/
theorem halfPhase_twistE_mul_self (w : List I) (μ : X) :
    ((halfPhase D (twistE (L := L) D β) true w μ : Lˣ) : L) *
      ((halfPhase D (twistE (L := L) D β) true w μ : Lˣ) : L) = 1 := by
  conv_lhs => arg 2; rw [← halfPhase_twistE_inv (L := L) (β := β) D true w μ]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem twistorModified_symm_positiveWord (w : List I) (μ : X) :
    (twistorModified D hβ ht q hC).symm (positiveWord D (t * q) 1 w μ) =
      ((halfPhase D (twistE (L := L) D β) true w μ : Lˣ) : L) • positiveWord D q (-1) w μ := by
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  change halfWord D (t * q) 1 true w μ = twistor D hβ ht q hC
    (((halfPhase D (twistE (L := L) D β) true w μ : Lˣ) : L) • halfWord D q (-1) true w μ)
  rw [map_smul, twistor_halfWord_true, smul_smul, halfPhase_twistE_mul_self, one_smul]

include hβ ht hC in
/-- At `π = -1` the nondegeneracy input follows from the one at `π = 1` and parameter `tq`, by
transport along the twistor. -/
theorem positiveFormNondegenerate_neg_one_of_twist
    (h : PositiveFormNondegenerate D L (t * q) 1 (one_pow 2)) :
    PositiveFormNondegenerate D L q (-1) neg_one_sq := by
  intro B hB hval x hx
  set e := twistorModified D hβ ht q hC
  let B' : LinearMap.BilinForm L (modified D (t * q) 1) := LinearMap.BilinForm.congr e B
  have hB' (x y) : B' x y = B (e.symm x) (e.symm y) := LinearMap.BilinForm.congr_apply _ _ _ _
  have hadj : ∀ u x y, B' (u * x) y = B' x (rhoModified D (t * q) 1 (one_pow 2) u * y) := by
    intro u x y
    rw [hB', hB', twistorModified_symm_mul, twistorModified_symm_mul, hB,
      twistorModified_symm_rhoModified]
  have hpos : ∀ a b μ ν, B' (positiveWord D (t * q) 1 a μ) (positiveWord D (t * q) 1 b ν) =
      if μ = ν then D.form (t * q) 1 (monomial L a) (monomial L b) else 0 := by
    intro a b μ ν
    rw [hB', twistorModified_symm_positiveWord, twistorModified_symm_positiveWord,
      LinearMap.map_smul₂, map_smul, hval, smul_eq_mul, smul_eq_mul]
    split_ifs with hμν
    · subst hμν
      rw [← form_twist_monomial D hβ ht q hC a b μ]
      have ha := halfPhase_twistE_mul_self (L := L) (β := β) D a μ
      have hb := Units.mul_inv (halfPhase D (twistE (L := L) D β) true b μ)
      linear_combination (((halfPhase D (twistE (L := L) D β) true b μ : Lˣ) : L) *
        (((halfPhase D (twistE (L := L) D β) true b μ)⁻¹ : Lˣ) : L) *
        D.form (t * q) 1 (monomial L a) (monomial L b)) * ha +
        D.form (t * q) 1 (monomial L a) (monomial L b) * hb
    · rw [mul_zero, mul_zero]
  have hex := h B' hadj hpos (e x) fun y ↦ by rw [hB', LinearEquiv.symm_apply_apply, hx]
  simpa using hex

end Twistor

/-! ### Flatness of the specializations -/

/-- The specialization `π ↦ ε` makes `ℚ(q)` a flat module over the covering ring: it is a direct
summand, cut out by the idempotent `(1 + επ)/2`. -/
theorem specialize_flat (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) :
    letI := (Coefficients.specialize ε hε).toRingHom.toAlgebra
    Module.Flat Coefficients.Ring (RatFunc ℚ) := by
  let _ := (Coefficients.specialize ε hε).toRingHom.toAlgebra
  have hsm (r : Coefficients.Ring) (c : RatFunc ℚ) :
      r • c = Coefficients.specialize ε hε r * c := Algebra.smul_def r c
  let i : RatFunc ℚ →ₗ[Coefficients.Ring] Coefficients.Ring :=
    { toFun := fun c ↦ algebraMap (RatFunc ℚ) Coefficients.Ring c * Coefficients.signIdempotent ε
      map_add' := fun c d ↦ by rw [map_add, add_mul]
      map_smul' := fun r c ↦ by
        rw [hsm, map_mul, RingHom.id_apply, smul_eq_mul, mul_comm (algebraMap _ _ _), mul_assoc,
          Coefficients.specialize_mul_signIdempotent, mul_left_comm] }
  refine Module.Flat.of_retract i (Algebra.linearMap Coefficients.Ring (RatFunc ℚ)) ?_
  ext c
  change Coefficients.specialize ε hε (algebraMap (RatFunc ℚ) Coefficients.Ring c *
    Coefficients.signIdempotent ε) = c
  rw [map_mul, AlgHom.commutes, Coefficients.signIdempotent, map_mul, map_add, map_mul,
    AlgHom.commutes, AlgHom.commutes, Coefficients.specialize_pi, map_one]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [show ε * ε = 1 by rw [← sq, hε]]
  norm_num

omit [DecidableEq I] in
/-- Coefficient change fixes the monomials of the free half algebra. -/
theorem mapCoeffs_monomial {k k' : Type*} [CommRing k] [CommRing k'] (φ : k →+* k')
    (w : List I) : FreeAlgebra.mapCoeffs φ (monomial k w) = monomial k' w := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [monomial_cons, map_mul, θ, FreeAlgebra.mapCoeffs_ι, ih]

/-! ### Assembly -/

section Assembly

open GenericTensor

/-- The image `q ↦ X ∈ L` of the generic parameter in a field extension `L` of `ℚ(q)`. -/
def genericParameter (L : Type*) [Field L] [Algebra (RatFunc ℚ) L] : Lˣ :=
  Units.map (algebraMap (RatFunc ℚ) L).toMonoidHom (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

/-- The values of `positiveModifiedForm` on pairs of positive words. -/
theorem positiveModifiedForm_positiveWord (a b : List I) (μ ν : X) :
    positiveModifiedForm D (positiveWord D Coefficients.q Coefficients.pi a μ)
        (positiveWord D Coefficients.q Coefficients.pi b ν) =
      if μ = ν then D.form Coefficients.q Coefficients.pi (monomial Coefficients.Ring a)
        (monomial Coefficients.Ring b) else 0 := by
  split_ifs with hμν
  · subst hμν
    have hw (w : List I) : positiveWord D Coefficients.q Coefficients.pi w μ =
        positiveHalf D Coefficients.q Coefficients.pi μ
          (D.toSerreF Coefficients.q Coefficients.pi (monomial Coefficients.Ring w)) :=
      Subtype.ext (halfMap_monomial D Coefficients.q Coefficients.pi true w μ).symm
    rw [hw, hw, positiveModifiedForm_positiveHalf, SuperCartanDatum.serreForm_toSerreF]
  · exact positiveModifiedForm_orthogonal D _ _ _ _ _ _
      (halfWord_mem_block D Coefficients.q Coefficients.pi true a μ)
      (halfWord_mem_block D Coefficients.q Coefficients.pi true b ν) (Or.inr hμν)

/-- One specialization `π ↦ ε`: the nondegeneracy input over a field `L ⊇ ℚ(q)` at `π' = ε`
gives the hypothesis of `Coefficients.leftRadical_trivial_of_specialize`. -/
theorem specialize_leftRadical_trivial (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) (L : Type*) [Field L]
    [Algebra (RatFunc ℚ) L] (π' : L) (hπ' : algebraMap (RatFunc ℚ) L ε = π')
    (hπ'2 : π' ^ 2 = 1) (h : PositiveFormNondegenerate D L (genericParameter L) π' hπ'2) :
    letI := (Coefficients.specialize ε hε).toRingHom.toAlgebra
    ∀ t : RatFunc ℚ ⊗[Coefficients.Ring] modified D Coefficients.q Coefficients.pi,
      (∀ s, (positiveModifiedForm D).baseChange (RatFunc ℚ) t s = 0) → t = 0 := by
  let _ := (Coefficients.specialize ε hε).toRingHom.toAlgebra
  have := specialize_flat ε hε
  let qK : (RatFunc ℚ)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero
  have hq : algebraMap Coefficients.Ring (RatFunc ℚ) (Coefficients.q : Coefficients.Ring) =
      (qK : RatFunc ℚ) := Coefficients.specialize_q ε hε
  have hπ : algebraMap Coefficients.Ring (RatFunc ℚ) Coefficients.pi = ε :=
    Coefficients.specialize_pi ε hε
  have hqL : algebraMap (RatFunc ℚ) L (qK : RatFunc ℚ) = (genericParameter L : L) := rfl
  set B := positiveModifiedForm D
  set BK := baseChangeForm D hq hπ B
  set BL := baseChangeForm D hqL hπ' BK
  have hadjK := baseChangeForm_adjoint D hq hπ B Coefficients.pi_sq hε
    (positiveModifiedForm_adjoint D)
  have hadjL := baseChangeForm_adjoint D hqL hπ' BK hε hπ'2 hadjK
  have hvalK := baseChangeForm_positiveWord D hq hπ B _ (positiveModifiedForm_positiveWord D)
  have hvalL := baseChangeForm_positiveWord D hqL hπ' BK _ hvalK
  let φ : Coefficients.Ring →+* L :=
    (algebraMap (RatFunc ℚ) L).comp (algebraMap Coefficients.Ring (RatFunc ℚ))
  have hφq : Units.map φ.toMonoidHom Coefficients.q = genericParameter L := by
    ext
    change algebraMap (RatFunc ℚ) L (algebraMap Coefficients.Ring (RatFunc ℚ) Coefficients.q) = _
    rw [hq, hqL]
  have hφπ : φ Coefficients.pi = π' := by
    change algebraMap (RatFunc ℚ) L (algebraMap Coefficients.Ring (RatFunc ℚ) Coefficients.pi) = _
    rw [hπ, hπ']
  have hvals : ∀ a b μ ν, BL (positiveWord D (genericParameter L) π' a μ)
      (positiveWord D (genericParameter L) π' b ν) =
        if μ = ν then D.form (genericParameter L) π' (monomial L a) (monomial L b) else 0 := by
    intro a b μ ν
    rw [hvalL]
    split_ifs
    · rw [← mapCoeffs_monomial φ a, ← mapCoeffs_monomial φ b]
      refine (PreF.form_mapCoeffs φ _ _ _ _ (fun i j ↦ ?_) (fun i ↦ ?_) _ _).symm
      · rw [D.map_chi φ, hφq, hφπ]
      · rw [D.map_norm φ _ _ i (Coefficients.denominator_isUnit D.toSuperCartanDatum i), hφq, hφπ]
    · simp
  have hK := leftRadical_trivial_of_baseChangeForm D hqL hπ' BK (h BL hadjL hvals)
  intro t ht
  have h0 : modifiedBaseChange D hq hπ t = 0 := hK _ fun y ↦ by
    rw [baseChangeForm_apply, LinearEquiv.symm_apply_apply]
    exact ht _
  simpa using h0

variable [Finite I] (hD : D.toSuperCartanDatum.BarConsistent)

include hD in
/-- Reduction of the nondegeneracy statement of Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1,
for the `ρ`-adjoint form `positiveModifiedForm` to the `π = 1` input. For a field `L ⊇ ℚ(q)`
containing a square root `t` of `-1`, if the `π = 1` input holds over `L` at the parameters `q`
and `tq`, then `positiveModifiedForm` has trivial left radical. The `π = 1` input is a hypothesis,
to be discharged from Lusztig's form ([Lus] 26.3.1). -/
theorem positiveModifiedForm_leftRadical_trivial (hα : LinearIndependent ℤ D.α)
    (L : Type*) [Field L] [Algebra (RatFunc ℚ) L] {t : Lˣ} (ht : t ^ 2 = -1)
    (h₁ : PositiveFormNondegenerate D L (genericParameter L) 1 (one_pow 2))
    (h₂ : PositiveFormNondegenerate D L (t * genericParameter L) 1 (one_pow 2)) :
    ∀ x, (∀ y, positiveModifiedForm D x y = 0) → x = 0 := by
  let _ : LinearOrder I := LinearOrder.lift' (Finite.equivFin I) (Finite.equivFin I).injective
  have h₃ : PositiveFormNondegenerate D L (genericParameter L) (-1) neg_one_sq :=
    positiveFormNondegenerate_neg_one_of_twist D (D.rootCoord_add_α hα) ht _ hD h₂
  have hm : (-1 : RatFunc ℚ) ^ 2 = 1 := by norm_num
  have hp := specialize_leftRadical_trivial D 1 (one_pow 2) L 1 (map_one _) (one_pow 2) h₁
  have hn := specialize_leftRadical_trivial D (-1) hm L (-1) (by simp) neg_one_sq h₃
  have key := @Coefficients.leftRadical_trivial_of_specialize
    (modified D Coefficients.q Coefficients.pi) _ _ (positiveModifiedForm D)
  exact key hp hn

include hD in
/-- The same reduction over the algebraic closure of `ℚ(q)`, with the `π = 1` input at `q` and at
`tq` for every square root `t` of `-1`. -/
theorem positiveModifiedForm_leftRadical_trivial_algebraicClosure (hα : LinearIndependent ℤ D.α)
    (h₁ : PositiveFormNondegenerate D (AlgebraicClosure (RatFunc ℚ))
      (genericParameter (AlgebraicClosure (RatFunc ℚ))) 1 (one_pow 2))
    (h₂ : ∀ t : (AlgebraicClosure (RatFunc ℚ))ˣ, t ^ 2 = -1 →
      PositiveFormNondegenerate D (AlgebraicClosure (RatFunc ℚ))
        (t * genericParameter (AlgebraicClosure (RatFunc ℚ))) 1 (one_pow 2)) :
    ∀ x, (∀ y, positiveModifiedForm D x y = 0) → x = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (-1 : AlgebraicClosure (RatFunc ℚ))
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have ht : Units.mk0 z hz0 ^ 2 = -1 := Units.ext (by simp [sq, ← hz])
  exact positiveModifiedForm_leftRadical_trivial D hD hα _ ht h₁ (h₂ _ ht)

include hD in
/-- The sesquilinear form `sesquilinearForm = positiveModifiedForm ∘ ψ` has trivial left radical
under the same `π = 1` input, since `ψ` is an involution. -/
theorem sesquilinearForm_leftRadical_trivial (hα : LinearIndependent ℤ D.α)
    (L : Type*) [Field L] [Algebra (RatFunc ℚ) L] {t : Lˣ} (ht : t ^ 2 = -1)
    (h₁ : PositiveFormNondegenerate D L (genericParameter L) 1 (one_pow 2))
    (h₂ : PositiveFormNondegenerate D L (t * genericParameter L) 1 (one_pow 2)) :
    ∀ x, (∀ y, sesquilinearForm D x y = 0) → x = 0 := by
  intro x hx
  have h0 := positiveModifiedForm_leftRadical_trivial D hD hα L ht h₁ h₂ (psiModified D x)
    fun y ↦ by rw [← sesquilinearForm_apply]; exact hx y
  rw [← psiModified_psiModified D x, h0, map_zero]

end Assembly

end OddMath.CoveringQuantum.UDot
