/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorSerre

/-!
# Negative operators on the actual highest/lowest tensor

With source parameter v=q^-1, Clark's Delta1 sends F to F tensor K^-1 + 1 tensor F;
Delta2 sends F to F tensor K^-1 + J tensor F. The first-factor parity operator
implements the super tensor sign. The lowest factor is the original Clark-omega
twist, whose F is pi_i J_i E, not the inverse twist. Negative Serre follows from
covering Serre additivity with the two tensor summands exchanged.

The datum is finite and bar-consistent, but weights are arbitrary and roots need
not be independent. No tensor integrability or form nondegeneracy is asserted.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (Λ Μ : X)

local instance : AddCommGroup
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  TensorProduct.addCommGroup

/-- Source tilde J on the actual highest quotient. -/
def tensorJ (i : I) : Module.End Coefficients.Ring (IntegrableQuotient D Λ) :=
  integrableWeight D Λ (fun μ ↦ D.pii pi i ^ (D.h i μ).natAbs)

/-- Source tilde K on the actual highest quotient (v=q^-1). -/
def tensorK (i : I) : Module.End Coefficients.Ring (IntegrableQuotient D Λ) :=
  integrableWeight D Λ (tensorToralScalar D false i)

/-- Global negative operator of the actual Clark-omega twist. The pi_i J_i
factor is essential; this is not the inverse omega action. -/
def lowestF (i : I) : Module.End Coefficients.Ring (IntegrableQuotient D Μ) :=
  integrableChevalley D Μ true i *
    integrableWeight D Μ (fun μ ↦ pi ^ (D.parl i (-μ)).val)

/-- The first-factor Koszul operator in Delta(F), with J exactly for Delta2. -/
def tensorFTwist (withJ : Bool) (i : I) :
    Module.End Coefficients.Ring (IntegrableQuotient D Λ) :=
  (if withJ then 1 else tensorJ D Λ i) * integrableParity D Λ i

/-- Actual Delta1/Delta2 negative tensor operator. The second original quotient
has negative weight in its omega twist, so its source K inverse is tensorK. -/
def tensorF (withJ : Bool) (i : I) : Module.End Coefficients.Ring
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  TensorProduct.map (integrableChevalley D Λ false i) (tensorK D Μ i) +
    TensorProduct.map (tensorFTwist D Λ withJ i) (lowestF D Μ i)

@[simp] theorem tensorF_tmul (withJ : Bool) (i : I)
    (x : IntegrableQuotient D Λ) (y : IntegrableQuotient D Μ) :
    tensorF D Λ Μ withJ i (x ⊗ₜ[Coefficients.Ring] y) =
      integrableChevalley D Λ false i x ⊗ₜ[Coefficients.Ring] tensorK D Μ i y +
        tensorFTwist D Λ withJ i x ⊗ₜ[Coefficients.Ring] lowestF D Μ i y := rfl

/-- The global negative operator agrees with the original omega-twisted action
at every weight, not merely on the lowest vector. -/
theorem lowestF_project (i : I) (μ : X) (x : IntegrableQuotient D Μ) :
    lowestF D Μ i (lowestRepresentation D Μ (one D Coefficients.q pi μ) x) =
      lowestRepresentation D Μ (F D Coefficients.q pi i μ) x := by
  change (integrableChevalley D Μ true i *
    integrableWeight D Μ (fun ν ↦ pi ^ (D.parl i (-ν)).val))
      (integrableRepresentation D Μ (clarkOmega D (one D Coefficients.q pi μ)) x) =
    integrableRepresentation D Μ (clarkOmega D (F D Coefficients.q pi i μ)) x
  rw [clarkOmega_one, Module.End.mul_apply, integrableWeight_project, neg_neg,
    map_smul, integrableChevalley_project, clarkOmega_F, map_smul, LinearMap.smul_apply]
  rfl

/-- Global mixed commutator inherited from all original weight-labelled relations. -/
theorem integrableChevalley_mixed (i j : I) :
    integrableChevalley D Λ true i * integrableChevalley D Λ false j -
      pi ^ (D.parity i * D.parity j).val •
        (integrableChevalley D Λ false j * integrableChevalley D Λ true i) =
      if i = j then integrableWeight D Λ
        (fun μ ↦ qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i μ)) else 0 := by
  apply LinearMap.ext
  intro x
  induction x using integrable_weight_induction D Λ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | project μ x =>
    have he := integrableChevalley_project D Λ true i μ x
    have hf := integrableChevalley_project D Λ false j μ x
    have hfe := integrableChevalley_project D Λ false j (μ + D.α i)
      (integrableRepresentation D Λ (E D Coefficients.q pi i μ) x)
    have hef := integrableChevalley_project D Λ true i (μ - D.α j)
      (integrableRepresentation D Λ (F D Coefficients.q pi j μ) x)
    simp only [halfGen, ite_true] at he hef
    simp only [halfGen, Bool.false_eq_true, ite_false] at hf hfe
    have hpE : integrableRepresentation D Λ (one D Coefficients.q pi (μ + D.α i))
        (integrableRepresentation D Λ (E D Coefficients.q pi i μ) x) =
        integrableRepresentation D Λ (E D Coefficients.q pi i μ) x := by
      rw [← Module.End.mul_apply, ← map_mul, one_mul_E_self]
    have hpF : integrableRepresentation D Λ (one D Coefficients.q pi (μ - D.α j))
        (integrableRepresentation D Λ (F D Coefficients.q pi j μ) x) =
        integrableRepresentation D Λ (F D Coefficients.q pi j μ) x := by
      rw [← Module.End.mul_apply, ← map_mul, one_mul_F_self]
    rw [hpE] at hfe
    rw [hpF] at hef
    have hm := congrArg (fun u ↦ integrableRepresentation D Λ u x)
      (comm_rel D Coefficients.q pi i j μ)
    simp only [map_sub, map_mul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.mul_apply] at hm
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, he, hf, hef, hfe]
    rw [hm]
    split_ifs <;> simp [integrableWeight_project]

theorem tensorJ_eq_smul (i : I) :
    tensorJ D Λ i = D.pii pi i ^ (D.h i Λ).natAbs • 1 := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D Λ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx
  | word w =>
    simp only [tensorJ, integrableWeight_word, map_sub,
      pii_pow_sub_word D pi pi_sq, LinearMap.smul_apply, Module.End.one_apply]

omit [DecidableEq I] [DecidableEq X] in
private theorem parl_word (i : I) (w : List I) :
    D.parl i (Λ - halfWeight D true (wordWeight w)) = D.parl i Λ := by
  induction w generalizing Λ with
  | nil => simp
  | cons j w ih =>
    simp only [wordWeight_cons, halfWeight_add, halfWeight_single, halfRoot, ite_true,
      ← sub_sub, ih, D.parl_sub_α]

omit [DecidableEq I] [DecidableEq X] in
private theorem parl_neg (i : I) (μ : X) : D.parl i (-μ) = D.parl i μ := by
  simp only [RootDatum.parl, RootDatum.h, map_neg, Int.cast_neg]
  have hn : ∀ z : ZMod 2, -z = z := by decide
  rw [hn]

theorem lowestF_eq_smul (i : I) :
    lowestF D Μ i = pi ^ (D.parl i (-Μ)).val • integrableChevalley D Μ true i := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D Μ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx
  | word w =>
    simp only [lowestF, Module.End.mul_apply, integrableWeight_word, parl_neg,
      parl_word, map_smul, LinearMap.smul_apply]

theorem tensorFTwist_eq_smul (withJ : Bool) (i : I) :
    tensorFTwist D Λ withJ i =
      (if withJ then 1 else D.pii pi i ^ (D.h i Λ).natAbs) • integrableParity D Λ i := by
  cases withJ <;> simp [tensorFTwist, tensorJ_eq_smul]

theorem integrableWeight_smul (c : Coefficients.Ring) (f : X → Coefficients.Ring) :
    integrableWeight D Λ (fun μ ↦ c * f μ) = c • integrableWeight D Λ f := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D Λ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx
  | word w => simp only [integrableWeight_word, LinearMap.smul_apply, smul_smul]

theorem tensorK_E (i j : I) :
    tensorK D Λ i * integrableChevalley D Λ true j =
      qp Coefficients.q (-D.dot i j) •
        (integrableChevalley D Λ true j * tensorK D Λ i) := by
  apply LinearMap.ext
  intro x
  simp only [tensorK, Module.End.mul_apply, integrableWeight_chevalley, halfRoot,
    ite_true, tensorToralScalar_add_root, LinearMap.smul_apply]
  rw [integrableWeight_smul, LinearMap.smul_apply, map_smul]

theorem tensorK_comm (i j : I) :
    Commute (tensorK D Λ i) (tensorK D Λ j) := by
  change tensorK D Λ i * tensorK D Λ j = tensorK D Λ j * tensorK D Λ i
  simp only [tensorK, integrableWeight_mul]
  congr 1
  funext μ
  exact mul_comm _ _

theorem tensorFTwist_chevalley (withJ : Bool) (i j : I) (positive : Bool) :
    tensorFTwist D Λ withJ i * integrableChevalley D Λ positive j =
      pi ^ (D.parity i * D.parity j).val •
        (integrableChevalley D Λ positive j * tensorFTwist D Λ withJ i) := by
  apply LinearMap.ext
  intro x
  simp only [tensorFTwist_eq_smul, Module.End.mul_apply, LinearMap.smul_apply,
    integrableParity_chevalley, map_smul]
  exact smul_comm _ _ _

theorem tensorFTwist_comm (withJ : Bool) (i j : I) :
    Commute (tensorFTwist D Λ withJ i) (tensorFTwist D Λ withJ j) := by
  change tensorFTwist D Λ withJ i * tensorFTwist D Λ withJ j =
    tensorFTwist D Λ withJ j * tensorFTwist D Λ withJ i
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D Λ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx
  | word w =>
    simp only [tensorFTwist_eq_smul, Module.End.mul_apply, LinearMap.smul_apply,
      integrableParity, integrableSign_word, map_smul, smul_smul]
    congr 1
    ring

omit [DecidableEq I] [DecidableEq X] in
private theorem scaled_serre {V : Type*} [AddCommGroup V] [Module Coefficients.Ring V]
    (e : I → Module.End Coefficients.Ring V) (c : I → Coefficients.Ring) (i j : I)
    (hs : ∑ r ∈ Finset.range (D.serreDeg i j + 1), D.serreCoeff Coefficients.q pi i j r •
      (e i ^ (D.serreDeg i j - r) * e j * e i ^ r) = 0) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1), D.serreCoeff Coefficients.q pi i j r •
      ((c i • e i) ^ (D.serreDeg i j - r) * (c j • e j) * (c i • e i) ^ r) = 0 := by
  have ht (r : ℕ) (hr : r ≤ D.serreDeg i j) :
      (c i • e i) ^ (D.serreDeg i j - r) * (c j • e j) * (c i • e i) ^ r =
        (c i ^ D.serreDeg i j * c j) • (e i ^ (D.serreDeg i j - r) * e j * e i ^ r) := by
    simp only [smul_pow, smul_mul_smul_comm]
    congr 1
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel hr]
  simp_rw [Finset.sum_congr rfl (fun r hr ↦ congrArg
    (fun v ↦ D.serreCoeff Coefficients.q pi i j r • v)
      (ht r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))))]
  simp_rw [smul_comm (D.serreCoeff Coefficients.q pi i j _)]
  rw [← Finset.smul_sum, hs, smul_zero]

theorem lowestF_serre {i j : I} (hij : i ≠ j) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1), D.serreCoeff Coefficients.q pi i j r •
      (lowestF D Μ i ^ (D.serreDeg i j - r) * lowestF D Μ j * lowestF D Μ i ^ r) = 0 := by
  simp only [lowestF_eq_smul]
  exact scaled_serre D (integrableChevalley D Μ true)
    (fun i ↦ pi ^ (D.parl i (-Μ)).val) i j (integrableChevalley_serre D Μ true hij)

private abbrev leftF (i : I) :=
  TensorProduct.map (integrableChevalley D Λ false i) (tensorK D Μ i)
private abbrev rightF (withJ : Bool) (i : I) :=
  TensorProduct.map (tensorFTwist D Λ withJ i) (lowestF D Μ i)

private theorem leftF_rightF (withJ : Bool) (i j : I) :
    leftF D Λ Μ i * rightF D Λ Μ withJ j =
      D.chi Coefficients.q pi i j • (rightF D Λ Μ withJ j * leftF D Λ Μ i) := by
  have hs : pi ^ (D.parity j * D.parity i).val * pi ^ (D.parity j * D.parity i).val = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
  have hp : integrableChevalley D Λ false i * tensorFTwist D Λ withJ j =
      pi ^ (D.parity j * D.parity i).val •
        (tensorFTwist D Λ withJ j * integrableChevalley D Λ false i) := by
    rw [tensorFTwist_chevalley, smul_smul, hs, one_smul]
  simp only [leftF, rightF, ← TensorProduct.map_mul, lowestF_eq_smul,
    mul_smul_comm, smul_mul_assoc, tensorK_E, hp]
  simp only [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul,
    SuperCartanDatum.chi_apply, qp]
  rw [mul_comm (D.parity j) (D.parity i)]
  congr 1
  ring

private theorem rightF_leftF (withJ : Bool) (i j : I) :
    rightF D Λ Μ withJ i * leftF D Λ Μ j =
      D.chi Coefficients.q⁻¹ pi i j • (leftF D Λ Μ j * rightF D Λ Μ withJ i) := by
  rw [leftF_rightF, smul_smul]
  have hc : D.chi Coefficients.q⁻¹ pi i j * D.chi Coefficients.q pi j i = 1 := by
    rw [(D.chi Coefficients.q pi).comm j i]
    simp only [SuperCartanDatum.chi_apply, inv_zpow, ← zpow_neg, neg_neg]
    have hp : pi ^ (D.parity i * D.parity j).val * pi ^ (D.parity i * D.parity j).val = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
    calc
      _ = ((Coefficients.q ^ D.dot i j : Coefficients.Ringˣ) : Coefficients.Ring) *
          ((Coefficients.q ^ (-D.dot i j) : Coefficients.Ringˣ) : Coefficients.Ring) *
          (pi ^ (D.parity i * D.parity j).val * pi ^ (D.parity i * D.parity j).val) := by ring
      _ = 1 := by rw [hp, ← Units.val_mul, ← zpow_add]; simp
  rw [hc, one_smul]

omit [DecidableEq I] [DecidableEq X] in
private theorem coveringSerre_coeff {B : Type*} [Ring B] [Algebra Coefficients.Ring B]
    (i j : I) (a b : B) :
    coveringSerre (D.qi Coefficients.q i) (D.pii pi i)
      (D.pii pi i ^ (D.parity j).val) (D.serreDeg i j) a b =
      ∑ r ∈ Finset.range (D.serreDeg i j + 1),
        D.serreCoeff Coefficients.q pi i j r • (a ^ (D.serreDeg i j - r) * b * a ^ r) := by
  unfold coveringSerre SuperCartanDatum.serreCoeff
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  rw [pow_add, ← pow_mul, mul_comm (D.parity j).val r]
  ring

private theorem serre_rightF (withJ : Bool) {i j : I} (hij : i ≠ j) :
    coveringSerre (D.qi Coefficients.q i) (D.pii pi i)
      (D.pii pi i ^ (D.parity j).val) (D.serreDeg i j)
        (rightF D Λ Μ withJ i) (rightF D Λ Μ withJ j) = 0 := by
  rw [coveringSerre_coeff]
  have ht : Commute (tensorFTwist D Λ withJ i) (tensorFTwist D Λ withJ j) :=
    tensorFTwist_comm D Λ withJ i j
  simp only [rightF, TensorProduct.map_pow, ← TensorProduct.map_mul]
  have hp (r : ℕ) (hr : r ≤ D.serreDeg i j) :
      tensorFTwist D Λ withJ i ^ (D.serreDeg i j - r) *
          tensorFTwist D Λ withJ j * tensorFTwist D Λ withJ i ^ r =
        tensorFTwist D Λ withJ i ^ D.serreDeg i j * tensorFTwist D Λ withJ j := by
    rw [mul_assoc, ← (ht.pow_left r).eq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hr]
  simp_rw [Finset.sum_congr rfl (fun r hr ↦ congrArg
    (fun f ↦ D.serreCoeff Coefficients.q pi i j r • TensorProduct.map f
      (lowestF D Μ i ^ (D.serreDeg i j - r) *
        lowestF D Μ j * lowestF D Μ i ^ r))
          (hp r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))))]
  have hs := congrArg (TensorProduct.mapBilinear (RingHom.id Coefficients.Ring) _ _ _ _
    (tensorFTwist D Λ withJ i ^ D.serreDeg i j * tensorFTwist D Λ withJ j))
      (lowestF_serre D Μ hij)
  simpa only [map_sum, map_smul, map_zero, TensorProduct.mapBilinear_apply] using hs

private theorem serre_leftF {i j : I} (hij : i ≠ j) :
    coveringSerre (D.qi Coefficients.q i) (D.pii pi i)
      (D.pii pi i ^ (D.parity j).val) (D.serreDeg i j)
        (leftF D Λ Μ i) (leftF D Λ Μ j) = 0 := by
  rw [coveringSerre_coeff]
  have ht : Commute (tensorK D Μ i) (tensorK D Μ j) :=
    tensorK_comm D Μ i j
  simp only [leftF, TensorProduct.map_pow, ← TensorProduct.map_mul]
  have hp (r : ℕ) (hr : r ≤ D.serreDeg i j) :
      tensorK D Μ i ^ (D.serreDeg i j - r) *
          tensorK D Μ j * tensorK D Μ i ^ r =
        tensorK D Μ i ^ D.serreDeg i j * tensorK D Μ j := by
    rw [mul_assoc, ← (ht.pow_left r).eq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hr]
  simp_rw [Finset.sum_congr rfl (fun r hr ↦ congrArg
    (fun f ↦ D.serreCoeff Coefficients.q pi i j r • TensorProduct.map
      (integrableChevalley D Λ false i ^ (D.serreDeg i j - r) *
        integrableChevalley D Λ false j * integrableChevalley D Λ false i ^ r) f)
          (hp r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))))]
  have hs := congrArg ((TensorProduct.mapBilinear (RingHom.id Coefficients.Ring) _ _ _ _).flip
    (tensorK D Μ i ^ D.serreDeg i j * tensorK D Μ j))
      (integrableChevalley_serre D Λ false hij)
  simpa only [map_sum, map_smul, map_zero, TensorProduct.mapBilinear_apply, LinearMap.flip_apply]
    using hs

/-- The complete negative Serre relation on arbitrary actual mixed tensor vectors.
Both Delta1 and Delta2, arbitrary Cartan entries, and both pi components are retained. -/
theorem tensorF_serre (withJ : Bool) {i j : I} (hij : i ≠ j) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1),
      D.serreCoeff Coefficients.q pi i j r •
        (tensorF D Λ Μ withJ i ^ (D.serreDeg i j - r) *
          tensorF D Λ Μ withJ j * tensorF D Λ Μ withJ i ^ r) = 0 := by
  rw [← coveringSerre_coeff D i j (tensorF D Λ Μ withJ i)
    (tensorF D Λ Μ withJ j)]
  have hN : D.serreDeg i j - 1 + 1 = D.serreDeg i j := by
    have := D.serreDeg_eq hij
    have := D.isGCM.offDiag_nonpos i j hij
    omega
  have hs := coveringSerre_add (D.qi Coefficients.q i) (D.pii_sq pi pi_sq i)
    (c := D.pii pi i ^ (D.parity j).val)
    (u := rightF D Λ Μ withJ i) (w := leftF D Λ Μ i)
    (b := rightF D Λ Μ withJ j) (b' := leftF D Λ Μ j)
    (D.serreDeg i j - 1) (by rw [hN]; exact D.odd_serreDeg_or pi hij)
    (by simpa only [D.chi_self, mul_comm] using leftF_rightF D Λ Μ withJ i i)
    (by simpa only [D.chi_of_ne Coefficients.q pi hij, mul_comm]
      using leftF_rightF D Λ Μ withJ i j)
    (by simpa only [D.chi_of_ne Coefficients.q⁻¹ pi hij, SuperCartanDatum.qi, inv_pow,
      mul_comm] using rightF_leftF D Λ Μ withJ i j)
  rw [hN, serre_rightF D Λ Μ withJ hij, serre_leftF D Λ Μ hij, add_zero] at hs
  simpa only [tensorF, add_comm] using hs

omit [DecidableEq I] [DecidableEq X] in
theorem tensor_pii_abs_add (i : I) (a b : ℤ) :
    D.pii pi i ^ (a + b).natAbs = D.pii pi i ^ a.natAbs * D.pii pi i ^ b.natAbs := by
  have hm : (a + b).natAbs % 2 = (a.natAbs + b.natAbs) % 2 := by
    rcases Int.natAbs_eq a with ha | ha <;>
      rcases Int.natAbs_eq b with hb | hb <;>
        rcases Int.natAbs_eq (a + b) with hab | hab <;> omega
  rw [← pow_add, ← Nat.div_add_mod (a + b).natAbs 2,
    ← Nat.div_add_mod (a.natAbs + b.natAbs) 2]
  simp only [pow_add, pow_mul, D.pii_sq pi pi_sq, one_pow, one_mul, hm]

omit [DecidableEq I] [DecidableEq X] in
theorem clarkOmega_coefficient (i : I) (μ : X) :
    pi ^ (D.parl i (-μ)).val = D.pii pi i * D.pii pi i ^ (D.h i μ).natAbs := by
  rw [parl_neg, pow_parl pi_sq, sub_eq_add_neg, tensor_pii_abs_add]
  simp only [Int.natAbs_neg, Int.natAbs_one, pow_one]
  exact mul_comm _ _

/-- The global lowest F retains the pi_i J_i factor of Clark omega. -/
theorem lowestF_eq_pii_J_E (i : I) :
    lowestF D Μ i = D.pii pi i •
      (tensorJ D Μ i * integrableChevalley D Μ true i) := by
  rw [lowestF_eq_smul, clarkOmega_coefficient, tensorJ_eq_smul,
    smul_mul_assoc, one_mul, smul_smul]

theorem tensorF_delta1 (i : I) :
    tensorF D Λ Μ true i =
      TensorProduct.map (integrableChevalley D Λ false i) (tensorK D Μ i) +
        TensorProduct.map (integrableParity D Λ i) (lowestF D Μ i) := by
  simp [tensorF, tensorFTwist]

theorem tensorF_delta2 (i : I) :
    tensorF D Λ Μ false i =
      TensorProduct.map (integrableChevalley D Λ false i) (tensorK D Μ i) +
        TensorProduct.map (tensorJ D Λ i * integrableParity D Λ i)
          (lowestF D Μ i) := rfl

/-- Inverse source K on the highest quotient; source K on its lowest twist. -/
def tensorKInv (i : I) : Module.End Coefficients.Ring (IntegrableQuotient D Λ) :=
  integrableWeight D Λ (fun μ ↦ qp Coefficients.q (D.d i * D.h i μ))

theorem tensorK_mul_inv (i : I) : tensorK D Λ i * tensorKInv D Λ i = 1 := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D Λ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx
  | word w =>
    simp only [tensorK, tensorKInv, Module.End.mul_apply, integrableWeight_word,
      map_smul, smul_smul, tensorToralScalar, Bool.false_eq_true, ite_false, one_mul,
      qp_mul, add_neg_cancel, qp_zero, one_smul, Module.End.one_apply]

theorem tensorK_inv_mul (i : I) : tensorKInv D Λ i * tensorK D Λ i = 1 := by
  rw [tensorKInv, tensorK, integrableWeight_mul]
  have h := tensorK_mul_inv D Λ i
  rw [tensorKInv, tensorK, integrableWeight_mul] at h
  convert h using 2
  funext μ
  exact mul_comm _ _

theorem tensorJ_mul_self (i : I) : tensorJ D Λ i * tensorJ D Λ i = 1 := by
  rw [tensorJ_eq_smul, smul_mul_smul_comm, ← pow_two, ← pow_mul,
    mul_comm _ 2, pow_mul, D.pii_sq pi pi_sq]
  simp

/-- Source K is group-like, with the second weight negated by omega. -/
def tensorGroupK (i : I) : Module.End Coefficients.Ring
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  TensorProduct.map (tensorK D Λ i) (tensorKInv D Μ i)

/-- Source J is group-like; negating a weight does not change its J eigenvalue. -/
def tensorGroupJ (i : I) : Module.End Coefficients.Ring
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  TensorProduct.map (tensorJ D Λ i) (tensorJ D Μ i)

@[simp] theorem tensorGroupK_tmul (i : I)
    (x : IntegrableQuotient D Λ) (y : IntegrableQuotient D Μ) :
    tensorGroupK D Λ Μ i (x ⊗ₜ[Coefficients.Ring] y) =
      tensorK D Λ i x ⊗ₜ[Coefficients.Ring] tensorKInv D Μ i y := rfl

@[simp] theorem tensorGroupJ_tmul (i : I)
    (x : IntegrableQuotient D Λ) (y : IntegrableQuotient D Μ) :
    tensorGroupJ D Λ Μ i (x ⊗ₜ[Coefficients.Ring] y) =
      tensorJ D Λ i x ⊗ₜ[Coefficients.Ring] tensorJ D Μ i y := rfl

end OddMath.CoveringQuantum.UDot.GenericVerma
