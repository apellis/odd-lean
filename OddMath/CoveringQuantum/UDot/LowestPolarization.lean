import OddMath.CoveringQuantum.UDot.IntegrableWeightOperators

/-!
# J-repair of the actual lowest-weight polarization

Clark omega and its inverse are not identified. The already descended J word
sign intertwines their actions on the actual source-generated quotient. Twisting
the original rho-adjoint form in its second argument therefore gives a genuine
same-action rho-polarization on the lowest quotient, with vacuum norm one.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open Coefficients PreF
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ : X)

omit [DecidableEq I] [DecidableEq X] [Finite I] in
private theorem parl_sub_word (i : I) (w : List I) :
    D.parl i (Λ - halfWeight D true (wordWeight w)) = D.parl i Λ := by
  induction w with
  | nil => simp
  | cons j w ih =>
    simp only [wordWeight_cons, halfWeight_add, halfWeight_single, halfRoot, ite_true]
    have hs := D.parl_add_α i j (Λ - D.α j - halfWeight D true (wordWeight w))
    have he : Λ - D.α j - halfWeight D true (wordWeight w) + D.α j =
        Λ - halfWeight D true (wordWeight w) := by abel
    rw [he] at hs
    rw [sub_add_eq_sub_sub]
    exact hs.symm.trans ih

omit [DecidableEq I] [DecidableEq X] [Finite I] in
/-- The accepted normalization sign is exactly the weight-block pi/J factor. -/
theorem polarizationSign_eq_parl (i : I) :
    polarizationSign D Λ i = pi ^ (D.parl i Λ).val := by
  have hp : ∀ p : ZMod 2, p = 0 ∨ p = 1 := by decide
  rcases hp (D.parity i) with hi | hi
  · simp [polarizationSign, SuperCartanDatum.pii, RootDatum.parl, hi]
  · simp only [polarizationSign, SuperCartanDatum.pii, hi, ZMod.val_one, pow_one,
      RootDatum.parl, one_mul]
    have he : (D.h i Λ).natAbs % 2 = ((D.h i Λ : ZMod 2)).val := by
      have h := Int.natAbs_eq (D.h i Λ)
      have hv := ZMod.val_intCast (n := 2) (D.h i Λ)
      rcases h with h | h <;> omega
    rw [← Nat.div_add_mod (D.h i Λ).natAbs 2, pow_add, pow_mul, pi_sq,
      one_pow, one_mul, he]
    generalize (D.h i Λ : ZMod 2) = z
    fin_cases z
    · change pi * pi ^ 0 = pi ^ 1
      rw [pow_zero, mul_one, pow_one]
    · change pi * pi ^ 1 = pi ^ 0
      rw [pow_one, pow_zero, ← pow_two, pi_sq]

/-- The block coefficient agrees with J's generator character whenever the
weight projector is nonzero; no weight-coset hypothesis is assumed. -/
theorem polarizationSign_project (i : I) (μ : X) (x : IntegrableQuotient D hD Λ) :
    polarizationSign D Λ i • integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x =
      pi ^ (D.parl i μ).val • integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x := by
  induction x using integrable_induction D hD Λ with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | smul c x hx => simp only [map_smul, smul_comm _ c, hx]
  | word w =>
    rw [integrableRepresentation_toIntegrable, representation_one, weightProject_mk,
      weightProjectFree_monomial]
    split_ifs with h
    · have hm : μ = Λ - halfWeight D true (wordWeight w) := by rw [h]; abel
      rw [hm, parl_sub_word, polarizationSign_eq_parl]
    · simp

/-- The character comparison holds on either weight-labelled Chevalley action. -/
theorem polarizationSign_halfGen (positive : Bool) (i : I) (μ : X)
    (x : IntegrableQuotient D hD Λ) :
    polarizationSign D Λ i • integrableRepresentation D hD Λ
      (halfGen D Coefficients.q pi positive i μ) x =
      pi ^ (D.parl i μ).val • integrableRepresentation D hD Λ
        (halfGen D Coefficients.q pi positive i μ) x := by
  simpa only [map_smul, integrableChevalley_project] using
    congrArg (integrableChevalley D hD Λ positive i)
      (polarizationSign_project D hD Λ i μ x)

omit [DecidableEq I] [DecidableEq X] [Finite I] in
private theorem parl_neg (i : I) (μ : X) : D.parl i (-μ) = D.parl i μ := by
  simp only [RootDatum.parl, RootDatum.h, map_neg, Int.cast_neg]
  have hn : ∀ z : ZMod 2, -z = z := by decide
  rw [hn]

/-- J repairs the inverse omega twist on the entire actual presentation. -/
theorem lowest_J_intertwine
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi)
    (x : IntegrableQuotient D hD Λ) :
    integrableJ D hD Λ (lowestRepresentation D hD Λ u x) =
      lowestInverseRepresentation D hD Λ u (integrableJ D hD Λ x) := by
  obtain ⟨u, rfl⟩ := mk_surjective D Coefficients.q pi u
  induction u using FreeAlgebra.induction generalizing x with
  | grade0 c => simp
  | grade1 g =>
    cases g with
    | one μ =>
      change integrableJ D hD Λ (lowestRepresentation D hD Λ (one D Coefficients.q pi μ) x) =
        lowestInverseRepresentation D hD Λ (one D Coefficients.q pi μ) (integrableJ D hD Λ x)
      simp only [lowestRepresentation_one, lowestInverseRepresentation, AlgHom.comp_apply,
        clarkOmegaInv_one]
      induction x using integrable_induction D hD Λ with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | smul c x hx => simp only [map_smul, hx]
      | word w =>
        simp only [integrableRepresentation_toIntegrable, representation_one,
          weightProject_mk, weightProjectFree_monomial, integrableJ_word, map_smul]
        split_ifs <;> simp [integrableJ_word]
    | e i μ =>
      change integrableJ D hD Λ (lowestRepresentation D hD Λ (E D Coefficients.q pi i μ) x) =
        lowestInverseRepresentation D hD Λ (E D Coefficients.q pi i μ) (integrableJ D hD Λ x)
      simp only [lowestRepresentation_E, lowestInverseRepresentation, AlgHom.comp_apply,
        clarkOmegaInv_E, map_smul, LinearMap.smul_apply]
      rw [integrableJ, integrableSign_F]
      exact polarizationSign_halfGen D hD Λ false i (-μ) _
    | f i μ =>
      change integrableJ D hD Λ (lowestRepresentation D hD Λ (F D Coefficients.q pi i μ) x) =
        lowestInverseRepresentation D hD Λ (F D Coefficients.q pi i μ) (integrableJ D hD Λ x)
      simp only [lowestRepresentation_F, lowestInverseRepresentation, AlgHom.comp_apply,
        clarkOmegaInv_F, map_smul, LinearMap.smul_apply]
      rw [integrableJ, integrableSign_E]
      have hs := polarizationSign_halfGen D hD Λ true i (-μ)
        (integrableJ D hD Λ x)
      change polarizationSign D Λ i • integrableRepresentation D hD Λ
        (E D Coefficients.q pi i (-μ)) _ = _ at hs
      simp only [integrableJ, halfGen, ite_true] at hs
      rw [hs, parl_neg, smul_smul, ← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, pi_sq,
        one_pow, one_smul]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | mul a b ha hb => simp only [map_mul, Module.End.mul_apply, ha, hb]

/-- Original form with precisely the accepted J/word sign in its second argument. -/
def lowestPolarization (hΛ : ∀ i, 0 ≤ D.h i Λ) :
    LinearMap.BilinForm Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  (integrablePolarization D hD Λ hΛ).compl₂ (integrableJ D hD Λ)

/-- Same-action rho-adjointness on the genuine lowest quotient, with J present. -/
theorem lowestPolarization_adjoint (hΛ : ∀ i, 0 ≤ D.h i Λ)
    (u : CoveringUDot Coefficients.Ring D Coefficients.q pi)
    (x y : IntegrableQuotient D hD Λ) :
    lowestPolarization D hD Λ hΛ (lowestRepresentation D hD Λ u x) y =
      lowestPolarization D hD Λ hΛ x
        (lowestRepresentation D hD Λ (rho D Coefficients.q pi pi_sq u).unop y) := by
  change integrablePolarization D hD Λ hΛ _ (integrableJ D hD Λ y) =
    integrablePolarization D hD Λ hΛ x (integrableJ D hD Λ _)
  rw [lowest_cross_adjoint, lowest_J_intertwine]

@[simp] theorem lowestPolarization_vacuum (hΛ : ∀ i, 0 ≤ D.h i Λ) :
    lowestPolarization D hD Λ hΛ (toIntegrable D hD Λ 1) (toIntegrable D hD Λ 1) = 1 := by
  simp only [lowestPolarization, LinearMap.compl₂_apply, integrableJ_vacuum,
    integrablePolarization_highest]

end OddMath.CoveringQuantum.UDot.GenericVerma
