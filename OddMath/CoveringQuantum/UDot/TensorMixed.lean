/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorNegative

/-!
# Mixed commutators of the actual tensor operators

The two cross terms cancel with their original toral and Koszul factors. The
remaining same-colour terms combine by the covering quantum-integer addition
identity. Both Delta choices have the same original BE2 commutator coefficient.
All identities are endomorphism identities on the original quotient tensors.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (Λ Μ : X)

local instance : AddCommGroup
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  TensorProduct.addCommGroup

theorem tensorTwist_eq_smul (withJ : Bool) (i : I) :
    tensorTwist D Λ withJ i =
      (if withJ then D.pii pi i ^ (D.h i Λ).natAbs else 1) •
        (tensorK D Λ i * integrableParity D Λ i) := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D Λ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx
  | word w =>
    simp only [tensorTwist, tensorK, Module.End.mul_apply, LinearMap.smul_apply,
      integrableParity, integrableSign_word, map_smul, integrableWeight_word,
      tensorToralScalar, Bool.false_eq_true, ite_false, one_mul, map_sub,
      pii_pow_sub_word D pi pi_sq, smul_smul]
    congr 1
    ring

theorem integrableWeight_parity (f : X → Coefficients.Ring) (i : I) :
    Commute (integrableWeight D Λ f) (integrableParity D Λ i) := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D Λ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx
  | word w =>
    simp only [Module.End.mul_apply, integrableParity, integrableSign_word,
      map_smul, integrableWeight_word]
    exact smul_comm _ _ _

theorem integrableParity_mul_self (i : I) :
    integrableParity D Λ i * integrableParity D Λ i = 1 := by
  apply LinearMap.ext
  intro x
  exact integrableSign_involutive D Λ _ _ x

theorem tensorTwist_FTwist_comm (withJ : Bool) (i j : I) :
    Commute (tensorTwist D Λ withJ i) (tensorFTwist D Λ withJ j) := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D Λ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx
  | word w =>
    simp only [tensorTwist, tensorFTwist_eq_smul, Module.End.mul_apply,
      LinearMap.smul_apply, integrableParity, integrableSign_word,
      map_smul, integrableWeight_word, smul_smul]
    congr 1
    ring

theorem tensorTwist_FTwist_self (withJ : Bool) (i : I) :
    tensorTwist D Λ withJ i * tensorFTwist D Λ withJ i =
      tensorJ D Λ i * tensorK D Λ i := by
  rw [tensorTwist_eq_smul, tensorFTwist_eq_smul, smul_mul_smul_comm,
    mul_assoc, integrableParity_mul_self, mul_one, tensorJ_eq_smul, smul_mul_assoc, one_mul]
  cases withJ <;> simp

omit [DecidableEq I] [DecidableEq X] in
private theorem tensorK_sub_root (i j : I) (μ : X) :
    tensorToralScalar D false i (μ - D.α j) =
      qp Coefficients.q (D.dot i j) * tensorToralScalar D false i μ := by
  simp only [tensorToralScalar, Bool.false_eq_true, ite_false, one_mul, map_sub, D.h_α]
  rw [show -(D.d i * (D.h i μ - D.a i j)) =
    D.dot i j + -(D.d i * D.h i μ) by simp [SuperCartanDatum.dot]; ring]
  simp only [qp, zpow_add, Units.val_mul]

theorem tensorK_F (i j : I) :
    tensorK D Λ i * integrableChevalley D Λ false j =
      qp Coefficients.q (D.dot i j) •
        (integrableChevalley D Λ false j * tensorK D Λ i) := by
  apply LinearMap.ext
  intro x
  simp only [tensorK, Module.End.mul_apply, integrableWeight_chevalley, halfRoot,
    Bool.false_eq_true, ite_false, ← sub_eq_add_neg, tensorK_sub_root, LinearMap.smul_apply]
  rw [integrableWeight_smul, LinearMap.smul_apply, map_smul]

theorem tensorTwist_F (withJ : Bool) (i j : I) :
    tensorTwist D Λ withJ i * integrableChevalley D Λ false j =
      D.chi Coefficients.q⁻¹ pi i j •
        (integrableChevalley D Λ false j * tensorTwist D Λ withJ i) := by
  have hp : integrableParity D Λ i * integrableChevalley D Λ false j =
      pi ^ (D.parity i * D.parity j).val •
        (integrableChevalley D Λ false j * integrableParity D Λ i) := by
    apply LinearMap.ext
    intro x
    exact integrableParity_chevalley D Λ i j false x
  simp only [tensorTwist_eq_smul, smul_mul_assoc, mul_smul_comm, mul_assoc, hp]
  rw [← mul_assoc, tensorK_F]
  simp only [smul_mul_assoc, smul_smul, mul_assoc, SuperCartanDatum.chi_apply,
    inv_zpow, ← zpow_neg, neg_neg, qp]
  congr 1
  ring

private theorem representation_mixed_project {V : Type*} [AddCommGroup V]
    [Module Coefficients.Ring V]
    (R : CoveringUDot Coefficients.Ring D Coefficients.q pi →ₐ[Coefficients.Ring]
      Module.End Coefficients.Ring V)
    (e f : I → Module.End Coefficients.Ring V)
    (he : ∀ i μ x, e i (R (one D Coefficients.q pi μ) x) = R (E D Coefficients.q pi i μ) x)
    (hf : ∀ i μ x, f i (R (one D Coefficients.q pi μ) x) = R (F D Coefficients.q pi i μ) x)
    (i j : I) (μ : X) (x : V) :
    (e i * f j - pi ^ (D.parity i * D.parity j).val • (f j * e i))
      (R (one D Coefficients.q pi μ) x) =
      if i = j then qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i μ) •
        R (one D Coefficients.q pi μ) x else 0 := by
  have hfe := hf j (μ + D.α i) (R (E D Coefficients.q pi i μ) x)
  have hef := he i (μ - D.α j) (R (F D Coefficients.q pi j μ) x)
  have hpE : R (one D Coefficients.q pi (μ + D.α i)) (R (E D Coefficients.q pi i μ) x) =
      R (E D Coefficients.q pi i μ) x := by
    rw [← Module.End.mul_apply, ← map_mul, one_mul_E_self]
  have hpF : R (one D Coefficients.q pi (μ - D.α j)) (R (F D Coefficients.q pi j μ) x) =
      R (F D Coefficients.q pi j μ) x := by
    rw [← Module.End.mul_apply, ← map_mul, one_mul_F_self]
  rw [hpE] at hfe
  rw [hpF] at hef
  have hm := congrArg (fun u ↦ R u x) (comm_rel D Coefficients.q pi i j μ)
  simp only [map_sub, map_mul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply] at hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, he, hf, hef, hfe]
  rw [hm]
  split_ifs <;> simp

theorem lowestE_project (i : I) (μ : X) (x : IntegrableQuotient D Μ) :
    integrableChevalley D Μ false i
      (lowestRepresentation D Μ (one D Coefficients.q pi μ) x) =
      lowestRepresentation D Μ (E D Coefficients.q pi i μ) x := by
  change integrableChevalley D Μ false i
      (integrableRepresentation D Μ (clarkOmega D (one D Coefficients.q pi μ)) x) =
    integrableRepresentation D Μ (clarkOmega D (E D Coefficients.q pi i μ)) x
  rw [clarkOmega_one, clarkOmega_E]
  exact integrableChevalley_project D Μ false i (-μ) x

theorem lowest_mixed (i j : I) :
    integrableChevalley D Μ false i * lowestF D Μ j -
      pi ^ (D.parity i * D.parity j).val •
        (lowestF D Μ j * integrableChevalley D Μ false i) =
      if i = j then integrableWeight D Μ
        (fun μ ↦ qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i (-μ))) else 0 := by
  apply LinearMap.ext
  intro x
  induction x using integrable_weight_induction D Μ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | project μ x =>
    have hm := representation_mixed_project D (lowestRepresentation D Μ)
      (integrableChevalley D Μ false) (lowestF D Μ)
      (lowestE_project D Μ) (lowestF_project D Μ) i j (-μ) x
    have hp : lowestRepresentation D Μ (one D Coefficients.q pi (-μ)) =
        integrableRepresentation D Μ (one D Coefficients.q pi μ) := by
      change integrableRepresentation D Μ (clarkOmega D (one D Coefficients.q pi (-μ))) = _
      rw [clarkOmega_one, neg_neg]
    rw [hp] at hm
    rw [hm]
    split_ifs <;> simp [integrableWeight_project]

private theorem tensor_mixed_expand (withJ : Bool) (i j : I) :
    tensorE D Λ Μ withJ i * tensorF D Λ Μ withJ j -
      pi ^ (D.parity i * D.parity j).val •
        (tensorF D Λ Μ withJ j * tensorE D Λ Μ withJ i) =
    TensorProduct.map
      (integrableChevalley D Λ true i * integrableChevalley D Λ false j -
        pi ^ (D.parity i * D.parity j).val •
          (integrableChevalley D Λ false j * integrableChevalley D Λ true i))
      (tensorK D Μ j) +
    TensorProduct.map (tensorTwist D Λ withJ i * tensorFTwist D Λ withJ j)
      (integrableChevalley D Μ false i * lowestF D Μ j -
        pi ^ (D.parity i * D.parity j).val •
          (lowestF D Μ j * integrableChevalley D Μ false i)) := by
  have hs : pi ^ (D.parity i * D.parity j).val * pi ^ (D.parity i * D.parity j).val = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
  have had : integrableChevalley D Λ true i * tensorFTwist D Λ withJ j =
      pi ^ (D.parity i * D.parity j).val •
        (tensorFTwist D Λ withJ j * integrableChevalley D Λ true i) := by
    rw [tensorFTwist_chevalley, mul_comm (D.parity j) (D.parity i), smul_smul, hs, one_smul]
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hadx := congrArg (fun f ↦ f x) had
  have ht := congrArg (fun f ↦ f x) (tensorTwist_F D Λ withJ i j)
  have hk := congrArg (fun f ↦ f y) (tensorK_F D Μ j i)
  have hc := congrArg (fun f ↦ f x) (tensorTwist_FTwist_comm D Λ withJ i j).eq
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at hadx ht hk hc
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.mul_apply, tensorE_tmul, tensorF_tmul, map_add,
      LinearMap.add_apply,
    map_tmul, sub_tmul, tmul_sub, smul_tmul, tmul_smul]
  rw [hadx, ht, hk, hc]
  simp only [smul_tmul, tmul_smul, SuperCartanDatum.chi_apply,
    inv_zpow, ← zpow_neg, neg_neg, qp, D.dot_comm j i, smul_add, smul_smul]
  rw [mul_comm (((Coefficients.q ^ D.dot i j : Coefficients.Ringˣ) : Coefficients.Ring))]
  abel

omit [DecidableEq I] [DecidableEq X] in
theorem tensor_qpInt_add (i : I) (a b : ℤ) :
    qpInt (D.qi Coefficients.q i) (D.pii pi i) a *
        ((D.qi Coefficients.q i ^ b : Coefficients.Ringˣ) : Coefficients.Ring) +
      D.pii pi i ^ a.natAbs *
        ((D.qi Coefficients.q i ^ (-a) : Coefficients.Ringˣ) : Coefficients.Ring) *
        qpInt (D.qi Coefficients.q i) (D.pii pi i) b =
      qpInt (D.qi Coefficients.q i) (D.pii pi i) (a + b) := by
  apply (vermaDenominator_isUnit D.toSuperCartanDatum i).mul_left_cancel
  calc
    _ = (vermaDenominator D.toSuperCartanDatum Coefficients.q pi i *
        qpInt (D.qi Coefficients.q i) (D.pii pi i) a) *
          ((D.qi Coefficients.q i ^ b : Coefficients.Ringˣ) : Coefficients.Ring) +
        D.pii pi i ^ a.natAbs *
          ((D.qi Coefficients.q i ^ (-a) : Coefficients.Ringˣ) : Coefficients.Ring) *
          (vermaDenominator D.toSuperCartanDatum Coefficients.q pi i *
            qpInt (D.qi Coefficients.q i) (D.pii pi i) b) := by ring
    _ = _ := by
      rw [denominator_qpInt D Coefficients.q pi pi_sq,
        denominator_qpInt D Coefficients.q pi pi_sq,
        denominator_qpInt D Coefficients.q pi pi_sq, tensor_pii_abs_add]
      simp only [neg_add, zpow_add, Units.val_mul]
      ring

/-- Every mixed commutator has the original BE2 quantum-integer coefficient on
all vectors of the actual total-weight projector, for both coproduct choices. -/
theorem tensor_mixed_project (withJ : Bool) (i j : I) (η : X) :
    (tensorE D Λ Μ withJ i * tensorF D Λ Μ withJ j -
      pi ^ (D.parity i * D.parity j).val •
        (tensorF D Λ Μ withJ j * tensorE D Λ Μ withJ i)) *
      tensorProject D Λ Μ η =
      if i = j then qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i η) •
        tensorProject D Λ Μ η else 0 := by
  rw [tensor_mixed_expand, integrableChevalley_mixed, lowest_mixed]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, tensorTwist_FTwist_self]
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
    induction y using integrable_induction D Μ with
    | zero => simp
    | add y z hy hz => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hy hz
    | smul c y hy => simpa only [tmul_smul, map_smul] using congrArg (c • ·) hy
    | word w =>
      simp only [Module.End.mul_apply, tensorProject_tmul_word, LinearMap.add_apply,
        map_tmul, tensorK, tensorJ, integrableWeight_project, integrableWeight_word,
        map_smul, LinearMap.smul_apply, smul_tmul, tmul_smul, smul_smul, ← add_smul]
      congr 1
      have hs := tensor_qpInt_add D i
        (D.h i (η + Μ - halfWeight D true (wordWeight w)))
        (-D.h i (Μ - halfWeight D true (wordWeight w)))
      have hq (ν : X) : tensorToralScalar D false i ν =
          ((D.qi Coefficients.q i ^ (-D.h i ν) : Coefficients.Ringˣ) : Coefficients.Ring) := by
        simp only [tensorToralScalar, Bool.false_eq_true, ite_false, one_mul,
          SuperCartanDatum.qi, qp, ← zpow_natCast, ← zpow_mul]
        congr 2
        ring
      simp only [hq, map_neg]
      have ha : D.h i (η + Μ - halfWeight D true (wordWeight w)) +
          -D.h i (Μ - halfWeight D true (wordWeight w)) = D.h i η := by
        simp only [map_sub, map_add]
        abel
      rw [ha] at hs
      convert hs using 1; ring
  · simp [hij]

end OddMath.CoveringQuantum.UDot.GenericVerma
