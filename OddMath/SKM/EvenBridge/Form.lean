/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.Datum
import OddMath.CoveringQuantum.Coefficients
import OddMath.CoveringQuantum.Ordinary
import OddMath.CoveringQuantum.PreF.BaseChange
import Categorification.QuantumGroup.UDotKL3
import Categorification.QuantumGroup.GabberKacBridge

/-!
# The half forms of Brundan–Ellis and of Khovanov–Lauda agree at `π = 1`

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §10 uses the form
`(θᵢ, θⱼ) = δᵢⱼ (1 - πᵢ qᵢ²)⁻¹` on the free algebra; A. D. Lauda, M. Khovanov, KL III
(arXiv:0807.3250) §2.1.1 uses `(θᵢ, θⱼ) = δᵢⱼ (1 - qᵢ²)⁻¹`, with the same bicharacter
`q^{-i·j}`. After specializing the covering parameter `π` to `1` (`specializeOne`), the two
forms agree on all elements (`specializeOne_form`); both are Lusztig's form at `v = q⁻¹`.
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open OddMath.CoveringQuantum Categorification.QuantumGroup

universe u v

variable {I : Type u} {X : Type v} [AddCommGroup X] [DecidableEq I]
  (R : CoveringQuantum.RootDatum I X)

/-- The specialization `π ↦ 1` of the covering coefficient ring `ℚ(q)[π]/(π² - 1)`. -/
abbrev specializeOne : Coefficients.Ring →ₐ[RatFunc ℚ] RatFunc ℚ :=
  Coefficients.specialize 1 (one_pow 2)

@[simp] theorem specializeOne_q : specializeOne (Coefficients.q : Coefficients.Ring) =
    ((UDot.KL3.qK : (RatFunc ℚ)ˣ) : RatFunc ℚ) :=
  Coefficients.specialize_q _ _

@[simp] theorem specializeOne_pi : specializeOne Coefficients.pi = 1 :=
  Coefficients.specialize_pi _ _

theorem specializeOne_qUnit :
    (Units.map specializeOne.toMonoidHom Coefficients.q : (RatFunc ℚ)ˣ) = UDot.KL3.qK := by
  refine Units.ext ?_
  rw [Units.coe_map]
  exact specializeOne_q

theorem specializeOne_qUnit_zpow (z : ℤ) :
    specializeOne ((Coefficients.q ^ z : Coefficients.Ringˣ) : Coefficients.Ring) =
      ((UDot.KL3.qK ^ z : (RatFunc ℚ)ˣ) : RatFunc ℚ) := by
  rw [← specializeOne_qUnit, ← map_zpow]
  rfl

omit [DecidableEq I] in
theorem catCartan_toLusztig : (catCartan R).toLusztig = R.lusztigDatum := by
  have key : ∀ a b : LusztigCartanDatum I, a.dot = b.dot → a = b := by
    rintro ⟨_, _, _, _, _, _⟩ ⟨_, _, _, _, _, _⟩ rfl; rfl
  exact key _ _ rfl

omit [DecidableEq I] in
/-- Inverse image of a word of `PreF` in the free algebra. -/
theorem equivFreeAlgebra_symm_word_ofList (u : List I) :
    ((Categorification.QuantumGroup.PreF.equivFreeAlgebra :
        FreeAlgebra (RatFunc ℚ) I ≃ₐ[RatFunc ℚ]
          Categorification.QuantumGroup.PreF (RatFunc ℚ) I).symm
        (Categorification.QuantumGroup.PreF.word (FreeMonoid.ofList u))) =
      CoveringQuantum.PreF.monomial (RatFunc ℚ) u := by
  induction u with
  | nil =>
    simp [CoveringQuantum.PreF.monomial, Categorification.QuantumGroup.PreF.word]
    rfl
  | cons i u ih =>
    rw [FreeMonoid.ofList_cons,
      Categorification.QuantumGroup.PreF.equivFreeAlgebra_symm_word_of_mul, ih]
    rfl

/-- At `π = 1` the Brundan–Ellis half form is the KL III half form `fF` with `q = qK` and
`(θᵢ, θᵢ) = (1 - qᵢ²)⁻¹`, on words. -/
theorem specializeOne_form (u w : List I) :
    specializeOne (R.form Coefficients.q Coefficients.pi
        (CoveringQuantum.PreF.monomial Coefficients.Ring u)
        (CoveringQuantum.PreF.monomial Coefficients.Ring w)) =
      UDot.fF (catCartan R) UDot.KL3.qK (UDot.KL3.cK (catCartan R))
        (Categorification.QuantumGroup.PreF.word (FreeMonoid.ofList u))
        (Categorification.QuantumGroup.PreF.word (FreeMonoid.ofList w)) := by
  have hmap : ∀ v : List I, FreeAlgebra.mapCoeffs specializeOne.toRingHom
      (CoveringQuantum.PreF.monomial Coefficients.Ring v) =
        CoveringQuantum.PreF.monomial (RatFunc ℚ) v := by
    intro v
    simp [CoveringQuantum.PreF.monomial, map_list_prod, CoveringQuantum.PreF.θ,
      Function.comp_def]
  rw [← CoveringQuantum.PreF.form_mapCoeffs specializeOne.toRingHom _ _ _ _
      (fun i j => R.map_chi specializeOne.toRingHom Coefficients.q Coefficients.pi i j)
      (fun i => R.map_norm specializeOne.toRingHom Coefficients.q Coefficients.pi i
        (Coefficients.denominator_isUnit _ i)),
    hmap, hmap]
  change R.form _ (specializeOne Coefficients.pi) _ _ = _
  rw [specializeOne_pi, specializeOne_qUnit, SuperCartanDatum.form_one, UDot.fF,
    show UDot.KL3.cK (catCartan R) =
        Categorification.QuantumGroup.lusztigC (catCartan R).dot UDot.KL3.qK⁻¹ from
      funext (UDot.KL3.cK_eq_lusztigC _),
    Categorification.QuantumGroup.PreF.form_equiv, equivFreeAlgebra_symm_word_ofList,
    equivFreeAlgebra_symm_word_ofList,
    catCartan_toLusztig, Units.val_inv_eq_inv_val]

end OddMath.SKM.EvenBridge
