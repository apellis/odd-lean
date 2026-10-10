import OddMath.CoveringQuantum.SerreForm
import LieLean.Algebra.QuantumGroup.GabberKac

/-!
# The ordinary specialization of the covering half algebra

At `π = 1`, the free form agrees with the pinned LieLean form at `v = q⁻¹`.
This change of variable matches both the bicharacter and the normalization.
The comparison uses the existing `LusztigCartanDatum` and `LusztigF` objects.
The finite-index, characteristic-zero, transcendental-parameter nondegeneracy theorem
`SuperCartanDatum.serreForm_one_nondegenerate` reuses LieLean's quantum Gabber–Kac result.
It is not a construction of the `π = -1` twisting comparison or a proof of covering
nondegeneracy before specialization.
-/

noncomputable section

namespace OddMath.CoveringQuantum

open LieLean LieLean.QuantumGroup

namespace SuperCartanDatum

variable {I : Type*} (C : SuperCartanDatum I)

/-- Forget parity while retaining the specified integral symmetrizer. -/
def lusztigDatum : LusztigCartanDatum I where
  dot := C.dot
  dot_comm := C.dot_comm
  dot_self_pos i := by rw [C.dot_self]; exact mul_pos (by decide) (by exact_mod_cast C.d_pos i)
  even_dot_self i := by rw [C.dot_self]; exact even_two.mul_right _
  dot_nonpos i j hij := C.dot_nonpos hij
  dot_self_dvd i j := by
    refine ⟨C.a i j, ?_⟩
    rw [C.dot_self, dot]
    ring

@[simp] theorem lusztigDatum_dot (i j : I) : C.lusztigDatum.dot i j = C.dot i j := rfl

@[simp] theorem lusztigDatum_d (i : I) : C.lusztigDatum.d i = C.d i := by
  have h := C.lusztigDatum.two_mul_d i
  rw [lusztigDatum_dot, C.dot_self] at h
  omega

@[simp] theorem lusztigDatum_cartanMatrix (i j : I) :
    C.lusztigDatum.cartanMatrix i j = C.a i j := by
  exact C.two_mul_dot_div i j

variable {k : Type*} [Field k] (q : kˣ)

/-- The scalar bicharacters match after inverting the quantum parameter. -/
theorem chi_one (i j : I) : C.chi q 1 i j = ((q : k)⁻¹) ^ C.lusztigDatum.dot i j := by
  simp [chi, zpow_neg, Units.val_zpow_eq_zpow_val]

/-- The generator normalizations match the same change of variable. -/
theorem norm_one (i : I) :
    C.norm q 1 i = LusztigF.thetaNorm C.lusztigDatum ((q : k)⁻¹) i := by
  simp [norm, pii, qi, LusztigF.thetaNorm, Ring.inverse_eq_inv,
    Units.val_pow_eq_pow_val, ← pow_mul]

variable [DecidableEq I]

/-- The skew derivatives of the two free-algebra constructions agree. -/
theorem rDeriv_one (i : I) :
    PreF.rDeriv (C.chi q 1) i = LusztigF.rDeriv C.lusztigDatum ((q : k)⁻¹) i := by
  have h : PreF.rMat (C.chi q 1) i = LusztigF.rMat C.lusztigDatum ((q : k)⁻¹) i := by
    apply FreeAlgebra.hom_ext
    funext j
    simp only [PreF.rMat, LusztigF.rMat, FreeAlgebra.lift_ι_apply, Function.comp_apply, C.chi_one]
  rw [PreF.rDeriv, LusztigF.rDeriv, h]
  rfl

/-- At `π = 1`, the covering free form is exactly the ordinary form at `q⁻¹`. -/
theorem form_one : C.form q 1 = LusztigF.form C.lusztigDatum ((q : k)⁻¹) := by
  have h : PreF.formEnd (C.chi q 1) (C.norm q 1) =
      LusztigF.formEnd C.lusztigDatum ((q : k)⁻¹) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [PreF.formEnd, LusztigF.formEnd, FreeAlgebra.lift_ι_apply,
      Function.comp_apply, C.norm_one, C.rDeriv_one]
  unfold form PreF.form LusztigF.form
  rw [h]

end SuperCartanDatum

variable {k : Type*} [Field k] (q : kˣ)

/-- The ordinary quantum integers are the specialization of the covering integers. -/
theorem qpNat_one_eq_qInt (n : ℕ) : qpNat q 1 n = qInt (q : k) n := by
  simp [qpNat, qInt, Units.val_inv_eq_inv_val]

/-- The ordinary quantum binomials are the specialization of the covering binomials. -/
theorem qpBinom_one (n r : ℕ) : qpBinom q 1 n r = qBinomial (q : k) n r := by
  induction n generalizing r with
  | zero => cases r <;> rfl
  | succ n ih =>
    cases r with
    | zero => rfl
    | succ r => simp only [qpBinom_succ_succ, qBinomial, one_pow, one_mul,
        Units.val_inv_eq_inv_val, ih]

namespace SuperCartanDatum

variable {I : Type*} [DecidableEq I] (C : SuperCartanDatum I)

omit [DecidableEq I] in
/-- The covering Serre element specializes to the ordinary binomial Serre element. -/
theorem serreElt_one (i j : I) :
    C.serreElt q 1 i j = qSerre ((q : k) ^ C.d i) (C.serreDeg i j)
      (LusztigF.θ k i) (LusztigF.θ k j) := by
  simp only [serreElt, serreCoeff, pii, one_pow, mul_one, qpBinom_one, qi,
    Units.val_pow_eq_pow_val, qSerre]

variable [CharZero k] (hq : Transcendental ℚ (q : k))

include hq

omit [DecidableEq I] in
/-- The ordinary divided-power Serre generators belong to the covering Serre ideal at `π = 1`. -/
theorem ordinary_serreIdeal_le :
    LusztigF.serreIdeal C.lusztigDatum ((q : k)⁻¹) ≤ C.serreIdeal q 1 := by
  apply TwoSidedIdeal.span_le.mpr
  rintro x ⟨i, j, hij, rfl⟩
  have hqi : Transcendental ℚ ((q : k)⁻¹) := fun h ↦ hq (by simpa using h.inv)
  have hf := LusztigF.qFactorial_ne_zero_of_not_root (D := C.lusztigDatum)
    (inv_ne_zero q.ne_zero) (fun n hn ↦ LusztigF.pow_ne_one_of_transcendental hqi hn)
    i (C.serreDeg i j)
  apply (C.mem_serreIdeal q 1 _).mpr
  rw [LusztigF.serreElement, lusztigDatum_cartanMatrix, ← serreDeg, qSerreDiv_eq hf]
  rw [lusztigDatum_d, inv_pow, qSerre_inv, ← C.serreElt_one q, map_smul,
    C.toSerreF_serreElt q 1 hij, smul_zero]

variable [Finite I]

/-- The radical equals the Serre ideal in the ordinary specialization, by the pinned
LieLean quantum Gabber–Kac theorem. No parity or bar-consistency assumption is needed
when `π = 1`. The finite-index hypothesis is that of the reused theorem. -/
theorem serreIdeal_one_eq_radical :
    C.serreIdeal q 1 = PreF.radical (C.chi q 1) (C.norm q 1) := by
  apply le_antisymm (C.serreIdeal_le_radical q 1 (one_pow 2))
  intro x hx
  apply C.ordinary_serreIdeal_le q hq
  apply (LusztigF.forall_form_eq_zero_iff_mem_serreIdeal C.lusztigDatum
    (show Transcendental ℚ ((q : k)⁻¹) from fun h ↦ hq (by simpa using h.inv))).mp
  intro y
  rw [← C.form_one q]
  exact (PreF.mem_radical_iff _ _).mp hx y

/-- Nondegeneracy of the Serre-presented half form at `π = 1`, for a transcendental
quantum parameter over a characteristic-zero field and a finite index type. -/
theorem serreForm_one_nondegenerate :
    (C.serreForm q 1 (one_pow 2)).Nondegenerate :=
  (C.serreForm_nondegenerate_iff_ideal_eq q 1 (one_pow 2)).mpr
    (C.serreIdeal_one_eq_radical q hq)

end SuperCartanDatum

end OddMath.CoveringQuantum
