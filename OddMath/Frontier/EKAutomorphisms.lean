import OddMath.Frontier.EKPresentation

/-! EK1107.5610v2 §2.3, on the actual integral radical quotient.
All lifts below use the proved presentation, never a newly assumed relation.
Source disclosure: p19 printed (2.24) has λ_j λ_j; the fixed specification and
source superanti definition require λ_i λ_j. Controls refute the literal
printed exponent at [2,1]. No claim to prove that misprinted equation.
The elementary psi12 proof uses inverse-series uniqueness, not the unsupported
direct psi3-to-(2.26) transformation described on p21. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators TensorProduct
namespace OddMath.Frontier.EKAutomorphisms
open CompleteElementary (A)
open EKRadicalQuotient (Q pi)
open EKElementaryQuotient (h e)
open EKPresentation (psi1)

/-- Source triangular sign, including s(0)=1. -/
def s (n : ℕ) : ℤ := (-1)^((n+1).choose 2)
@[simp] theorem s_zero : s 0 = 1 := rfl
theorem s_square (n : ℕ) : s n * s n = 1 := by
  simp [s, ← pow_add, ← two_mul, pow_mul]
theorem s_succ (n : ℕ) : s (n+1) = (-1 : ℤ)^(n+1) * s n := by
  unfold s
  rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

theorem s_pair (a b : ℕ) (hab : Even (a+b)) : s a*s (b+1) = s (a+1)*s b := by
  have hp : (-1 : ℤ)^(a+1) = (-1 : ℤ)^(b+1) := by
    conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
    conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
    congr 1
    have := Nat.even_iff.mp hab
    omega
  rw [s_succ, s_succ, hp]
  ring

/-- Generator extension with explicit source relations, used only to descend
specified maps. This is not a hypothesis in any exported automorphism theorem. -/
def familyFree {C : Type*} [Ring C] (g : ℕ → C) : A →ₐ[ℤ] C :=
  FreeAlgebra.lift ℤ (fun n => g (n+1))
theorem familyFree_h {C : Type*} [Ring C] (g : ℕ → C) (h0 : g 0 = 1) (n : ℕ) :
    familyFree g (CompleteElementary.h n) = g n := by
  cases n with
  | zero => simpa using h0.symm
  | succ n => exact FreeAlgebra.lift_ι_apply _ n

def descend {C : Type*} [Ring C] (g : ℕ → C) (h0 : g 0 = 1)
    (hev : ∀ a b, Even (a+b) → g a*g b = g b*g a)
    (hod : ∀ a b, Even (a+b) →
      g a*g (b+1) + (-1 : ℤ)^a • (g (b+1)*g a) =
      (-1 : ℤ)^a • (g (a+1)*g b) + g b*g (a+1)) : Q →+* C := by
  let F := (familyFree g).toRingHom
  have hk : ∀ r ∈ EKPresentation.relIdeal, F r = 0 := by
    intro r hr
    rw [EKPresentation.relIdeal, EKPresentation.relTwoSided, TwoSidedIdeal.mem_asIdeal] at hr
    induction hr using TwoSidedIdeal.span_induction with
    | mem r hr =>
      cases hr with
      | even a b hab =>
        simpa only [F, map_sub, map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          familyFree_h g h0, sub_eq_zero] using hev a b hab
      | odd a b hb hab =>
        cases b with
        | zero => omega
        | succ b =>
          have he : Even (a+b) := by
            rw [Nat.even_iff]; have := Nat.odd_iff.mp hab; omega
          simpa only [F, map_sub, map_mul, map_add, map_zsmul, AlgHom.toRingHom_eq_coe,
            AlgHom.coe_toRingHom, familyFree_h g h0,
            Nat.add_sub_cancel, sub_eq_zero] using hod a b he
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | neg x _ hx => rw [map_neg, hx, neg_zero]
    | left_absorb a x _ hx => rw [map_mul, hx, mul_zero]
    | right_absorb a x _ hx => rw [map_mul, hx, zero_mul]
  exact (Ideal.Quotient.lift EKPresentation.relIdeal F hk).comp
    EKPresentation.presentationEquiv.symm.toRingHom

theorem descend_h {C : Type*} [Ring C] (g : ℕ → C) (h0 hev hod) (n : ℕ) :
    descend g h0 hev hod (h n) = g n := by
  rw [← EKPresentation.presentationEquiv_h]
  unfold descend
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  exact familyFree_h g h0 n

theorem hom_ext_h {C : Type*} [Ring C] (f g : Q →+* C)
    (he : ∀ n, f (h n) = g (h n)) : f = g := by
  have hh : (f.comp pi).toIntAlgHom = (g.comp pi).toIntAlgHom := by
    apply FreeAlgebra.hom_ext
    funext n
    exact he (n+1)
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := EKRadicalQuotient.pi_surjective x
  exact congrArg (fun k : A →ₐ[ℤ] C => k a) hh

theorem h_even (a b : ℕ) (hab : Even (a+b)) : h a*h b = h b*h a := by
  exact EKQuotientRelations.same_even false a b hab

theorem h_odd (a b : ℕ) (hab : Even (a+b)) :
    h a*h (b+1) + (-1 : ℤ)^a • (h (b+1)*h a) =
      (-1 : ℤ)^a • (h (a+1)*h b) + h b*h (a+1) :=
  EKQuotientRelations.same_odd_succ false a b hab

private theorem signed_even (a b : ℕ) (hab : Even (a+b)) :
    (s a • h a)*(s b • h b) = (s b • h b)*(s a • h a) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h_even a b hab, mul_comm (s a)]
private theorem signed_odd (a b : ℕ) (hab : Even (a+b)) :
    (s a • h a)*(s (b+1) • h (b+1)) + (-1 : ℤ)^a • ((s (b+1) • h (b+1))*(s a • h a)) =
    (-1 : ℤ)^a • ((s (a+1) • h (a+1))*(s b • h b)) + (s b • h b)*(s (a+1) • h (a+1)) := by
  have hh := congrArg (fun x : Q => (s a*s (b+1)) • x) (h_odd a b hab)
  simpa only [smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
    s_pair a b hab, mul_comm, mul_left_comm, mul_assoc] using hh

def psi2Hom : Q →+* Q := descend (fun n => s n • h n)
  (by simp [h]) signed_even signed_odd
@[simp] theorem psi2Hom_h (n : ℕ) : psi2Hom (h n) = s n • h n :=
  descend_h _ _ _ _ n

theorem psi2Hom_involutive (x : Q) : psi2Hom (psi2Hom x) = x := by
  have hh : psi2Hom.comp psi2Hom = RingHom.id Q := by
    apply hom_ext_h
    intro n
    simp only [RingHom.comp_apply, RingHom.id_apply, psi2Hom_h, map_zsmul, smul_smul,
      s_square, one_smul]
  exact congrArg (fun f : Q →+* Q => f x) hh

/-- EK's multiplicative involution on Q, not a coalgebra assertion. -/
def psi2 : Q ≃+* Q :=
  { psi2Hom with
    invFun := psi2Hom
    left_inv := psi2Hom_involutive
    right_inv := psi2Hom_involutive }
@[simp] theorem psi2_h (n : ℕ) : psi2 (h n) = s n • h n := psi2Hom_h n
@[simp] theorem psi2_involutive (x : Q) : psi2 (psi2 x) = x := psi2Hom_involutive x

/-- Composition order is psi1 after psi2. -/
def psi12 : Q ≃+* Q := psi2.trans psi1
@[simp] theorem psi12_apply (x : Q) : psi12 x = psi1 (psi2 x) := rfl
@[simp] theorem psi12_h (n : ℕ) : psi12 (h n) = s n • e n := by
  simp only [psi12_apply, psi2_h, map_zsmul, EKPresentation.psi1_h]

private def H : PowerSeries Q := PowerSeries.mk h
private def I : PowerSeries Q := PowerSeries.mk (fun n => s n • e n)
private theorem coeff_mul_fin {R : Type*} [Semiring R]
    (f g : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff R n (f*g) =
      ∑ i : Fin (n+1), PowerSeries.coeff R i f * PowerSeries.coeff R (n-i) g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]

private theorem I_H : I*H = 1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_fin, PowerSeries.coeff_one]
  simp only [I, H, PowerSeries.coeff_mk]
  cases n with
  | zero => simp [e, h]
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    have hh := congrArg pi (CompleteElementary.elementary_complete_inverse n)
    simpa only [map_sum, map_mul, map_zero, CompleteElementary.ekSign,
      map_pow, map_neg, map_one, e, h, s, zsmul_eq_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using hh

private theorem map_H : PowerSeries.map psi12.toRingHom H = I := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, H, I, PowerSeries.coeff_mk,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, psi12_h]

private theorem map_I : PowerSeries.map psi12.toRingHom I = H := by
  let F := PowerSeries.map psi12.toRingHom
  have hm : F I * I = 1 := by
    calc
      F I * I = F I * F H := by rw [show F H = I from map_H]
      _ = 1 := by rw [← map_mul, I_H, map_one]
  calc
    F I = F I * (I*H) := by rw [I_H, mul_one]
    _ = H := by rw [← mul_assoc, hm, one_mul]

/-- Equation (2.25) for elementary generators, proved by inverse-series
uniqueness rather than assumed on the quotient. -/
@[simp] theorem psi12_e (n : ℕ) : psi12 (e n) = s n • h n := by
  have hh := congrArg (PowerSeries.coeff Q n) map_I
  simp only [PowerSeries.coeff_map, I, H, PowerSeries.coeff_mk,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_zsmul] at hh
  have hs := congrArg (fun x : Q => s n • x) hh
  simpa only [smul_smul, s_square, one_smul] using hs

theorem psi12_involutive (x : Q) : psi12 (psi12 x) = x := by
  have hh : psi12.toRingHom.comp psi12.toRingHom = RingHom.id Q := by
    apply hom_ext_h
    intro n
    simp only [RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, psi12_h, map_zsmul, psi12_e, smul_smul, s_square, one_smul]
  exact congrArg (fun f : Q →+* Q => f x) hh

/-- Cor2.18, with genuine inverse and the exact composition order. -/
theorem psi2_psi1_psi2 (x : Q) : psi2 (psi1 (psi2 x)) = psi1.symm x := by
  apply psi1.injective
  rw [RingEquiv.apply_symm_apply]
  exact psi12_involutive x

theorem psi1_psi2_psi1 (x : Q) : psi1 (psi2 (psi1 x)) = psi2 x := by
  have hh := psi12_involutive (psi2 x)
  simpa only [psi12_apply, psi2_involutive] using hh

/-- Product of generator signs; no commuting or reordering of word factors. -/
def wordSign (w : List ℕ) : ℤ := (w.map s).prod

theorem psi2_word (w : List ℕ) :
    psi2 ((w.map h).prod) = wordSign w • (w.map h).prod := by
  induction w with
  | nil => simp [wordSign]
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, psi2_h, ih,
      smul_mul_assoc, mul_smul_comm, smul_smul, wordSign, mul_comm]

theorem psi12_hWord (w : List ℕ) :
    psi12 ((w.map h).prod) = wordSign w • (w.map e).prod := by
  induction w with
  | nil => simp [wordSign]
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, psi12_h, ih,
      smul_mul_assoc, mul_smul_comm, smul_smul, wordSign, mul_comm]

theorem psi12_eWord (w : List ℕ) :
    psi12 ((w.map e).prod) = wordSign w • (w.map h).prod := by
  induction w with
  | nil => simp [wordSign]
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, psi12_e, ih,
      smul_mul_assoc, mul_smul_comm, smul_smul, wordSign, mul_comm]

theorem sign_square (n : ℕ) : (-1 : ℤ)^n * (-1 : ℤ)^n = 1 := by
  simp [← pow_add, ← two_mul, pow_mul]

private theorem reverse_even (a b : ℕ) (hab : Even (a+b)) :
    MulOpposite.op (h a)*MulOpposite.op (h b) = MulOpposite.op (h b)*MulOpposite.op (h a) := by
  apply MulOpposite.unop_injective
  exact (h_even a b hab).symm
private theorem reverse_odd (a b : ℕ) (hab : Even (a+b)) :
    MulOpposite.op (h a)*MulOpposite.op (h (b+1)) +
      (-1 : ℤ)^a • (MulOpposite.op (h (b+1))*MulOpposite.op (h a)) =
    (-1 : ℤ)^a • (MulOpposite.op (h (a+1))*MulOpposite.op (h b)) +
      MulOpposite.op (h b)*MulOpposite.op (h (a+1)) := by
  apply MulOpposite.unop_injective
  change h (b+1)*h a + (-1 : ℤ)^a • (h a*h (b+1)) =
    (-1 : ℤ)^a • (h b*h (a+1)) + h (a+1)*h b
  have hh := congrArg (fun x : Q => (-1 : ℤ)^a • x) (h_odd a b hab)
  simpa only [smul_add, smul_smul, sign_square, one_smul, add_comm] using hh

/-- Auxiliary ORDINARY reversal. It is deliberately not named psi3. -/
def reverseHom : Q →+* Qᵐᵒᵖ := descend (fun n => MulOpposite.op (h n))
  (by simp [h]) reverse_even reverse_odd

def reverseLinear : Q →ₗ[ℤ] Q where
  toFun x := MulOpposite.unop (reverseHom x)
  map_add' x y := by rw [map_add reverseHom x y]; rfl
  map_smul' r x := by
    rw [map_zsmul reverseHom r x]
    rfl
@[simp] theorem reverse_h (n : ℕ) : reverseLinear (h n) = h n := by
  change MulOpposite.unop (reverseHom (h n)) = _
  rw [show reverseHom (h n) = MulOpposite.op (h n) from descend_h _ _ _ _ n]
  rfl
@[simp] theorem reverse_one : reverseLinear 1 = 1 := by simp [reverseLinear]
theorem reverse_mul (x y : Q) : reverseLinear (x*y) = reverseLinear y*reverseLinear x := by
  simp [reverseLinear]

theorem reverse_word (w : List ℕ) :
    reverseLinear ((w.map h).prod) = (w.reverse.map h).prod := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [List.map_cons, List.prod_cons, reverse_mul, reverse_h,
      ih, List.reverse_cons, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, List.map_nil, List.prod_nil, mul_one]

/-- Linear diagonal twist by total degree; not asserted multiplicative. -/
def degreeTwist : Q →ₗ[ℤ] Q := EKIntegralBases.hBasis.constr ℤ
  (fun μ => s μ.card • EKIntegralBases.hBasis μ)
@[simp] theorem degreeTwist_partition (μ : YoungDiagram) :
    degreeTwist (EKPartitionSpanning.hPartition μ) = s μ.card • EKPartitionSpanning.hPartition μ := by
  simp [degreeTwist, ← EKIntegralBases.hBasis_apply]

theorem degreeTwist_homogeneous {d : ℕ} {x : Q} (hx : x ∈ EKIntegralBases.degreePiece d) :
    degreeTwist x = s d • x := by
  rw [EKIntegralBases.degreePiece_eq_hPartition_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    change degreeTwist (EKPartitionSpanning.hPartition μ.val) = _
    rw [degreeTwist_partition, μ.property]
    rfl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]
  | smul r x _ hx => simp only [map_smul, hx, smul_comm r]

theorem hWord_degree (w : List ℕ) : (w.map h).prod ∈ EKIntegralBases.degreePiece w.sum :=
  EKIntegralBases.hWord_mem_degreePiece w

theorem degreeTwist_word (w : List ℕ) :
    degreeTwist ((w.map h).prod) = s w.sum • (w.map h).prod :=
  degreeTwist_homogeneous (hWord_degree w)

/-- The source super-reversal: triangular degree twist after signed ordinary
reversal. Its super sign is proved below, not hidden in an assumed structure. -/
def psi3Linear : Q →ₗ[ℤ] Q := degreeTwist.comp
  (reverseLinear.comp psi2.toRingHom.toIntAlgHom.toLinearMap)

theorem psi3_word (w : List ℕ) :
    psi3Linear ((w.map h).prod) = (s w.sum * wordSign w) • (w.reverse.map h).prod := by
  change degreeTwist (reverseLinear (psi2 ((w.map h).prod))) = _
  rw [psi2_word, map_smul, reverse_word, map_smul, degreeTwist_word, List.sum_reverse,
    smul_smul, mul_comm (wordSign w)]

@[simp] theorem wordSign_reverse (w : List ℕ) : wordSign w.reverse = wordSign w := by
  simp [wordSign, List.map_reverse]
theorem wordSign_square (w : List ℕ) : wordSign w*wordSign w = 1 := by
  induction w with
  | nil => simp [wordSign]
  | cons a w ih =>
    change (s a*wordSign w)*(s a*wordSign w) = 1
    calc
      _ = (s a*s a)*(wordSign w*wordSign w) := by ring
      _ = 1 := by rw [s_square, ih, mul_one]

theorem psi3_word_involutive (w : List ℕ) :
    psi3Linear (psi3Linear ((w.map h).prod)) = (w.map h).prod := by
  rw [psi3_word, map_smul, psi3_word, List.reverse_reverse, List.sum_reverse,
    wordSign_reverse, smul_smul]
  have hs : (s w.sum * wordSign w)*(s w.sum * wordSign w) = 1 := by
    calc
      _ = (s w.sum*s w.sum)*(wordSign w*wordSign w) := by ring
      _ = 1 := by rw [s_square, wordSign_square, mul_one]
  rw [hs, one_smul]

theorem psi3Linear_involutive (x : Q) : psi3Linear (psi3Linear x) = x := by
  induction x using EKPairingAdjoint.basis_induction EKIntegralBases.hBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hb μ r =>
    simp only [map_smul, EKIntegralBases.hBasis_apply]
    exact congrArg (fun x : Q => r • x) (psi3_word_involutive μ.rowLens)

def psi3 : Q ≃ₗ[ℤ] Q :=
  { psi3Linear with
    invFun := psi3Linear
    left_inv := psi3Linear_involutive
    right_inv := psi3Linear_involutive }
@[simp] theorem psi3_involutive (x : Q) : psi3 (psi3 x) = x := psi3Linear_involutive x
@[simp] theorem psi3_h (n : ℕ) : psi3 (h n) = h n := by
  have hh := psi3_word [n]
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.sum_cons, List.sum_nil, add_zero, wordSign, List.reverse_singleton,
    s_square, one_smul] using hh

abbrev psi1L : Q →ₗ[ℤ] Q := psi1.toRingHom.toIntAlgHom.toLinearMap
abbrev psi2L : Q →ₗ[ℤ] Q := psi2.toRingHom.toIntAlgHom.toLinearMap

private theorem preserves_degree_of_words (f : Q →ₗ[ℤ] Q)
    (hf : ∀ w : List ℕ, f ((w.map h).prod) ∈ EKIntegralBases.degreePiece w.sum)
    {d : ℕ} {x : Q} (hx : x ∈ EKIntegralBases.degreePiece d) :
    f x ∈ EKIntegralBases.degreePiece d := by
  rw [EKIntegralBases.degreePiece_eq_hPartition_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    have hh := hf μ.val.rowLens
    simpa only [EKIntegralBases.rowLens_sum, μ.property] using hh
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (EKIntegralBases.degreePiece d).add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using (EKIntegralBases.degreePiece d).smul_mem r hx

theorem psi1_degree {d : ℕ} {x : Q} (hx : x ∈ EKIntegralBases.degreePiece d) :
    psi1 x ∈ EKIntegralBases.degreePiece d := by
  apply preserves_degree_of_words psi1L _ hx
  intro w
  change psi1 ((w.map h).prod) ∈ _
  rw [EKPresentation.psi1_word, EKIntegralBases.degreePiece_eq_ePartition_span]
  exact EKIntegralBases.word_mem_partitionPiece true w

theorem psi2_degree {d : ℕ} {x : Q} (hx : x ∈ EKIntegralBases.degreePiece d) :
    psi2 x ∈ EKIntegralBases.degreePiece d := by
  apply preserves_degree_of_words psi2L _ hx
  intro w
  change psi2 ((w.map h).prod) ∈ _
  rw [psi2_word]
  exact Submodule.smul_mem _ _ (hWord_degree w)

theorem reverse_degree {d : ℕ} {x : Q} (hx : x ∈ EKIntegralBases.degreePiece d) :
    reverseLinear x ∈ EKIntegralBases.degreePiece d := by
  apply preserves_degree_of_words reverseLinear _ hx
  intro w
  rw [reverse_word]
  simpa only [List.sum_reverse] using hWord_degree w.reverse

theorem psi3_degree {d : ℕ} {x : Q} (hx : x ∈ EKIntegralBases.degreePiece d) :
    psi3 x ∈ EKIntegralBases.degreePiece d := by
  apply preserves_degree_of_words psi3Linear _ hx
  intro w
  rw [psi3_word]
  exact Submodule.smul_mem _ _ (by simpa only [List.sum_reverse] using hWord_degree w.reverse)

theorem psi1_inverse_degree {d : ℕ} {x : Q} (hx : x ∈ EKIntegralBases.degreePiece d) :
    psi1.symm x ∈ EKIntegralBases.degreePiece d := by
  rw [← psi2_psi1_psi2]
  exact psi2_degree (psi1_degree (psi2_degree hx))

theorem triangular_add (a b : ℕ) :
    (a+b+1).choose 2 = (a+1).choose 2 + (b+1).choose 2 + a*b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hh := Nat.choose_succ_succ (a+b+1) 1
    have hk := Nat.choose_succ_succ (b+1) 1
    simp only [Nat.choose_one_right, Nat.succ_eq_add_one] at hh hk
    rw [show a+(b+1)+1 = a+b+1+1 by omega, hh, hk, ih]
    ring

theorem s_add (a b : ℕ) : s (a+b) = s a*s b*(-1 : ℤ)^(a*b) := by
  simp only [s, triangular_add, pow_add]

theorem psi3_homogeneous {d : ℕ} {x : Q} (hx : x ∈ EKIntegralBases.degreePiece d) :
    psi3 x = s d • reverseLinear (psi2 x) :=
  degreeTwist_homogeneous (reverse_degree (psi2_degree hx))

/-- The defining super-anti multiplication law, for ALL homogeneous elements
of the actual quotient and all natural weights, including zero. -/
theorem psi3_mul {a b : ℕ} {x y : Q}
    (hx : x ∈ EKIntegralBases.degreePiece a) (hy : y ∈ EKIntegralBases.degreePiece b) :
    psi3 (x*y) = (-1 : ℤ)^(a*b) • (psi3 y*psi3 x) := by
  rw [psi3_homogeneous (EKIntegralBases.degreePiece_mul hx hy), map_mul, reverse_mul,
    psi3_homogeneous hx, psi3_homogeneous hy]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, s_add,
    mul_comm, mul_left_comm, mul_assoc]

/-- The literal sum over pairs i<j, expressed recursively by the first part. -/
def pairExponent : List ℕ → ℕ
  | [] => 0
  | a::w => a*w.sum + pairExponent w

theorem source_word_sign (w : List ℕ) : s w.sum * wordSign w = (-1 : ℤ)^(pairExponent w) := by
  induction w with
  | nil => simp [pairExponent, wordSign]
  | cons a w ih =>
    change s (a+w.sum)*(s a*wordSign w) = (-1 : ℤ)^(a*w.sum+pairExponent w)
    rw [s_add, pow_add, ← ih]
    calc
      _ = (s a*s a)*(s w.sum*wordSign w)*(-1 : ℤ)^(a*w.sum) := by ring
      _ = _ := by rw [s_square, one_mul, mul_comm]

/-- Word formula forced by the source superanti definition and fixed specification,
valid for arbitrary lists, even zero parts; see the printed-(2.24) disclosure. -/
theorem psi3_hWord (w : List ℕ) :
    psi3 ((w.map h).prod) = (-1 : ℤ)^(pairExponent w) • (w.reverse.map h).prod := by
  exact (psi3_word w).trans (congrArg (fun r : ℤ => r • (w.reverse.map h).prod) (source_word_sign w))

open EKIntegralBases (degreePiece)
open EKCoideal (quotientCoproduct)
open EKSignedQuotient (quotientTensorMul)

/-- Literal Koszul multiplication on arbitrary homogeneous quotient elements.
The four span inductions extend the inherited ordered-word theorem. -/
theorem tensorMul_homogeneous {a b c d : ℕ} {x y z t : Q}
    (hx : x ∈ degreePiece a) (hy : y ∈ degreePiece b)
    (hz : z ∈ degreePiece c) (ht : t ∈ degreePiece d) :
    quotientTensorMul (x ⊗ₜ[ℤ] y) (z ⊗ₜ[ℤ] t) =
      (-1 : ℤ)^(b*c) • ((x*z) ⊗ₜ[ℤ] (y*t)) := by
  rw [EKIntegralBases.degreePiece_eq_hPartition_span] at hx hy hz ht
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ν, rfl⟩ := hy
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨ρ, rfl⟩ := hz
        induction ht using Submodule.span_induction with
        | mem t ht =>
          obtain ⟨σ, rfl⟩ := ht
          simpa only [EKIntegralBases.pi_hWord, EKIntegralBases.rowLens_sum, ν.property, ρ.property] using
            EKSignedQuotient.quotientTensorMul_hWords μ.val.rowLens ν.val.rowLens ρ.val.rowLens σ.val.rowLens
        | zero => simp
        | add u v _ _ hu hv =>
          simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, LinearMap.add_apply,
            add_mul, mul_add, smul_add, hu, hv]
        | smul r u _ hu =>
          simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply,
            smul_mul_assoc, mul_smul_comm, RingHom.id_apply, hu, smul_comm r]
      | zero => simp
      | add u v _ _ hu hv =>
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, LinearMap.add_apply,
          add_mul, mul_add, smul_add, hu, hv]
      | smul r u _ hu =>
        simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply,
          smul_mul_assoc, mul_smul_comm, RingHom.id_apply, hu, smul_comm r]
    | zero => simp
    | add u v _ _ hu hv =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, LinearMap.add_apply,
        add_mul, mul_add, smul_add, hu, hv]
    | smul r u _ hu =>
      simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply,
        smul_mul_assoc, mul_smul_comm, RingHom.id_apply, hu, smul_comm r]
  | zero => simp
  | add u v _ _ hu hv =>
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, LinearMap.add_apply,
      add_mul, mul_add, smul_add, hu, hv]
  | smul r u _ hu =>
    simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply,
      smul_mul_assoc, mul_smul_comm, RingHom.id_apply, hu, smul_comm r]

/-- Tensor action on the exact tensor product carrying inherited signed multiplication. -/
def psi1Tensor : (Q ⊗[ℤ] Q) →ₗ[ℤ] (Q ⊗[ℤ] Q) := TensorProduct.map psi1L psi1L
@[simp] theorem psi1Tensor_tmul (x y : Q) :
    psi1Tensor (x ⊗ₜ[ℤ] y) = psi1 x ⊗ₜ[ℤ] psi1 y := rfl

private theorem psi1Tensor_homogeneous {a b c d : ℕ} {x y z t : Q}
    (hx : x ∈ degreePiece a) (hy : y ∈ degreePiece b)
    (hz : z ∈ degreePiece c) (ht : t ∈ degreePiece d) :
    psi1Tensor (quotientTensorMul (x ⊗ₜ[ℤ] y) (z ⊗ₜ[ℤ] t)) =
    quotientTensorMul (psi1Tensor (x ⊗ₜ[ℤ] y)) (psi1Tensor (z ⊗ₜ[ℤ] t)) := by
  rw [tensorMul_homogeneous hx hy hz ht, map_smul, psi1Tensor_tmul, map_mul, map_mul,
    psi1Tensor_tmul, psi1Tensor_tmul,
    tensorMul_homogeneous (psi1_degree hx) (psi1_degree hy) (psi1_degree hz) (psi1_degree ht)]

private theorem hBasis_degree (μ : YoungDiagram) : EKIntegralBases.hBasis μ ∈ degreePiece μ.card := by
  simpa only [EKIntegralBases.hBasis_apply, EKIntegralBases.rowLens_sum] using hWord_degree μ.rowLens

/-- Multiplicativity here is for the inherited SIGNED tensor multiplication. -/
theorem psi1Tensor_mul (u v : Q ⊗[ℤ] Q) :
    psi1Tensor (quotientTensorMul u v) = quotientTensorMul (psi1Tensor u) (psi1Tensor v) := by
  induction u using EKPairingAdjoint.basis_induction
      (EKIntegralBases.hBasis.tensorProduct EKIntegralBases.hBasis) with
  | hz => simp
  | ha u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  | hb p r =>
    induction v using EKPairingAdjoint.basis_induction
        (EKIntegralBases.hBasis.tensorProduct EKIntegralBases.hBasis) with
    | hz => simp
    | ha u v hu hv => simp only [map_add, hu, hv]
    | hb q s =>
      simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, Basis.tensorProduct_apply']
      exact congrArg (fun v : Q ⊗[ℤ] Q => s • r • v)
        (psi1Tensor_homogeneous (hBasis_degree p.1) (hBasis_degree p.2)
          (hBasis_degree q.1) (hBasis_degree q.2))

theorem coproduct_h (n : ℕ) :
    quotientCoproduct (h n) = ∑ i : Fin (n+1), h i ⊗ₜ[ℤ] h (n-i) := by
  simp only [h, EKCoideal.quotientCoproduct_pi, EKFreeCoproduct.coproduct_h,
    map_sum, EKCoideal.quotientTensorMap_tmul]

theorem psi1_coproduct_h (n : ℕ) :
    quotientCoproduct (psi1 (h n)) = psi1Tensor (quotientCoproduct (h n)) := by
  rw [EKPresentation.psi1_h, EKElementaryQuotient.quotientCoproduct_e, coproduct_h, map_sum]
  simp only [psi1Tensor_tmul, EKPresentation.psi1_h]

private theorem psi1_coproduct_word (w : List ℕ) :
    quotientCoproduct (psi1 ((w.map h).prod)) = psi1Tensor (quotientCoproduct ((w.map h).prod)) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, EKSignedQuotient.quotient_coproduct_mul,
      psi1_coproduct_h, ih, psi1Tensor_mul]

/-- Full bialgebra coproduct compatibility on arbitrary, also inhomogeneous, Q. -/
theorem psi1_coproduct (x : Q) :
    quotientCoproduct (psi1 x) = psi1Tensor (quotientCoproduct x) := by
  induction x using EKPairingAdjoint.basis_induction EKIntegralBases.hBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hb μ r =>
    simp only [map_zsmul, map_smul, EKIntegralBases.hBasis_apply]
    exact congrArg (fun x : Q ⊗[ℤ] Q => r • x) (psi1_coproduct_word μ.rowLens)

open EKRadicalQuotient (quotientCounit)
theorem counit_h (n : ℕ) : quotientCounit (h n) = if n=0 then 1 else 0 := by
  exact EKFreeCoproduct.counit_h n

theorem counit_hWord (w : List ℕ) :
    quotientCounit ((w.map h).prod) = if w.sum=0 then 1 else 0 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, counit_h, ih, List.sum_cons,
      Nat.add_eq_zero]
    split_ifs <;> simp_all

theorem counit_positive {d : ℕ} {x : Q} (hd : d ≠ 0) (hx : x ∈ degreePiece d) :
    quotientCounit x = 0 := by
  rw [EKIntegralBases.degreePiece_eq_hPartition_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    change quotientCounit ((μ.val.rowLens.map h).prod) = 0
    rw [counit_hWord, EKIntegralBases.rowLens_sum, μ.property, if_neg hd]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul r x _ hx => simp only [map_smul, hx, smul_zero]

theorem counit_e (n : ℕ) : quotientCounit (e n) = if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n; simp [e]
  · rw [if_neg hn]
    apply counit_positive hn
    rw [EKIntegralBases.degreePiece_eq_ePartition_span]
    exact EKIntegralBases.generator_mem true n

/-- Full counit compatibility, not merely a generator test. -/
theorem psi1_counit (x : Q) : quotientCounit (psi1 x) = quotientCounit x := by
  have hh : quotientCounit.toRingHom.comp psi1.toRingHom = quotientCounit.toRingHom := by
    apply hom_ext_h
    intro n
    change quotientCounit (psi1 (h n)) = quotientCounit (h n)
    rw [EKPresentation.psi1_h, counit_e, counit_h]
  exact congrArg (fun f : Q →+* ℤ => f x) hh

/-- Explicit source exponent in (2.25), without replacing it by a degree-only sign. -/
theorem wordSign_eq_pow (w : List ℕ) :
    wordSign w = (-1 : ℤ)^((w.map (fun n => (n+1).choose 2)).sum) := by
  induction w with
  | nil => simp [wordSign]
  | cons a w ih =>
    change s a * wordSign w = (-1 : ℤ)^((a+1).choose 2 + (w.map (fun n => (n+1).choose 2)).sum)
    rw [ih, pow_add]
    rfl

theorem psi12_hWord_source (w : List ℕ) :
    psi12 ((w.map h).prod) =
      (-1 : ℤ)^((w.map (fun n => (n+1).choose 2)).sum) • (w.map e).prod := by
  rw [psi12_hWord, wordSign_eq_pow]

theorem psi12_eWord_source (w : List ℕ) :
    psi12 ((w.map e).prod) =
      (-1 : ℤ)^((w.map (fun n => (n+1).choose 2)).sum) • (w.map h).prod := by
  rw [psi12_eWord, wordSign_eq_pow]

/-- Literal indexed sum over ordered positions i<j in the source (2.24). -/
theorem pairExponent_positions (w : List ℕ) :
    pairExponent w = ∑ i : Fin w.length, ∑ j : Fin w.length,
      if i < j then w.get i * w.get j else 0 := by
  induction w with
  | nil => simp [pairExponent]
  | cons a w ih =>
    have get_succ (i : Fin w.length) : (a::w).get i.succ = w.get i := rfl
    simp only [pairExponent, List.length_cons, Fin.sum_univ_succ, List.get_cons_zero,
      get_succ, Fin.succ_lt_succ_iff, Fin.not_lt_zero, ↓reduceIte,
      Fin.succ_pos, zero_add, add_zero]
    rw [← Finset.mul_sum]
    have hh : (∑ i : Fin w.length, w.get i) = w.sum := by
      simpa only [List.ofFn_get] using (List.sum_ofFn (f := w.get)).symm
    rw [hh, ih]

/-- Exact fixed-specification indexed word theorem, all lengths and all parts.
This uses i,j rather than the printed j,j typo in (2.24). -/
theorem psi3_hWord_source (w : List ℕ) :
    psi3 ((w.map h).prod) =
      (-1 : ℤ)^(∑ i : Fin w.length, ∑ j : Fin w.length,
        if i < j then w.get i * w.get j else 0) • (w.reverse.map h).prod := by
  rw [psi3_hWord, pairExponent_positions]

end OddMath.Frontier.EKAutomorphisms
