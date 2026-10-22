import OddMath

/-! HW Lemmas 5.7–5.8 (input to BE2 Prop 11.2) for the polynomial representation of the
nilHecke ring, a signed nilHecke family with `ε = 1`. -/
noncomputable section
open OddMath.QuiverHecke.SignedNilHecke Categorification.NilHecke Categorification.KLR.KL2.NH

example : chR (dd ℚ 3) 0 2 * (xv ℚ 3 0 ^ 2 * idem 1 0 3 (xv ℚ 3) (dd ℚ 3) 0 3) =
    ((1 : ℤ) ^ (2 : ℕ).choose 2) • idem 1 0 3 (xv ℚ 3) (dd ℚ 3) 0 3 := by
  simpa using (isSignedNilHeckeFamily_nilHecke ℚ 3).chR_mul_x_pow_mul_idem (s' := 0) (l := 2)
    (a := 2) le_rfl (by omega) le_rfl

example : chL (dd ℚ 3) 0 2 * (xv ℚ 3 2 ^ 1 * idem 1 0 3 (xv ℚ 3) (dd ℚ 3) 0 3) = 0 := by
  simpa using (isSignedNilHeckeFamily_nilHecke ℚ 3).chL_mul_x_pow_mul_idem (s' := 0) (l := 2)
    (a := 1) le_rfl (by omega) (by omega)

example : idem 1 0 3 (xv ℚ 3) (dd ℚ 3) 0 3 = demIdem ℚ 3 := idem_nilHecke ℚ 3

#print axioms IsSignedNilHeckeFamily.chR_mul_x_pow_mul_idem
#print axioms IsSignedNilHeckeFamily.chL_mul_x_pow_mul_idem
#print axioms IsSignedNilHeckeFamily.idem_mul_chL_mul_idem
#print axioms IsSignedNilHeckeFamily.idem_mul_chR_mul_idem
#print axioms IsSignedNilHeckeFamily.idem_mul_idem
#print axioms isSignedNilHeckeFamily_nilHecke
#print axioms idem_nilHecke
