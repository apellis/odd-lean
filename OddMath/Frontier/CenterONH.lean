import OddMath.Frontier.CenterONHRoot
import OddMath.Frontier.NilHeckeCenter

/-!
# The center of the odd symmetric kernel and of the odd nilHecke ring, all ranks

EKL arXiv:1111.1320v1, Prop. 2.15, p. 13 (corrected form; the printed ordinary-center
assertions are refuted in rank three by `NilHeckeCenter.prop215_counterexample`).

For every `n`, with `N = n + 2`, on the actual objects:

* `center_kernel` (R1): an element of the joint kernel `OΛ_N` of the odd divided
  differences is central in `OΛ_N` iff it is central in the whole skew polynomial
  ring `Pol_N`.
* `center_nilHecke` (R2): an element of the presented odd nilHecke ring
  `ONH_N` is central iff it is the dot image of an element of `OΛ_N ∩ Z(Pol_N)`.
* `s_invariant` (R3): elements of `OΛ_N ∩ Z(Pol_N)` are fixed by every signed
  simple transposition `s_i`.

Convention dependencies (the library's fixed sign conventions): `s_i(x_j) = -x_{s_i j}`;
`∂_i(fg) = ∂_i(f) g + s_i(f) ∂_i(g)`; `∂_i(x_i) = ∂_i(x_{i+1}) = 1`; End
multiplication is composition with the left factor acting last.
-/

namespace OddMath.Frontier.CenterONH
open OddMath.SkewPolynomial (SkewPolynomial generator monomial generator_anticommute)
open OddMath.Frontier.AllRankDivided OddMath.Frontier.OddSymmetricKernel
open OddMath.Frontier.NilHeckeAction
open OddMath.Frontier.ElementaryGeneration (square_comm)
noncomputable section

variable {n : ℕ}

/-! ## The intertwining identity -/

theorem squares_diff_comm (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    (generator i.castSucc ^ 2 - generator i.succ ^ 2) * f =
      f * (generator i.castSucc ^ 2 - generator i.succ ^ 2) := by
  rw [sub_mul, mul_sub, square_comm, square_comm]

/-- `(x_i - x_{i+1}) f - s_i(f) (x_i - x_{i+1}) = (x_i² - x_{i+1}²) ∂_i f`. -/
theorem intertwine (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    (generator i.castSucc - generator i.succ) * f - s i f * (generator i.castSucc - generator i.succ) =
      (generator i.castSucc ^ 2 - generator i.succ ^ 2) * divided i f := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) f
  induction x using Quotient.inductionOn' with
  | h w =>
    change _ * PbwL3.evalAlg (n+2) w - s i (PbwL3.evalAlg (n+2) w) * _ =
      _ * divided i (PbwL3.evalAlg (n+2) w)
    induction w using FreeAlgebra.induction with
    | grade0 r =>
        rw [AlgHom.commutes]
        change _ * (r • 1) - s i (r • 1) * _ = _ * divided i (r • 1)
        rw [map_zsmul, map_one, map_zsmul, divided_one, smul_zero, mul_zero,
          mul_smul_comm, smul_mul_assoc, mul_one, one_mul, sub_self]
    | grade1 j =>
        rw [PbwL3.evalAlg_ι, s_generator, divided_generator]
        by_cases ha : j = i.castSucc
        · subst ha
          rw [Equiv.swap_apply_left, if_pos (Or.inl rfl)]
          noncomm_ring
        · by_cases hb : j = i.succ
          · subst hb
            rw [Equiv.swap_apply_right, if_pos (Or.inr rfl)]
            noncomm_ring
          · rw [Equiv.swap_apply_of_ne_of_ne ha hb, if_neg (by tauto), mul_zero]
            have h1 : generator i.castSucc * generator j = -(generator j * generator i.castSucc) :=
              generator_anticommute i.castSucc j (Ne.symm ha)
            have h2 : generator i.succ * generator j = -(generator j * generator i.succ) :=
              generator_anticommute i.succ j (Ne.symm hb)
            rw [sub_mul, mul_sub, neg_mul, h1, h2]
            noncomm_ring
    | add a b ha hb =>
        rw [map_add, map_add, map_add, mul_add, add_mul, mul_add]
        rw [← ha, ← hb]
        abel
    | mul a b ha hb =>
        rw [map_mul, map_mul, divided_mul]
        set δ := (generator i.castSucc - generator i.succ : SkewPolynomial (n+2))
        set Q := (generator i.castSucc ^ 2 - generator i.succ ^ 2 : SkewPolynomial (n+2)) with hQ
        set U := PbwL3.evalAlg (n+2) a
        set V := PbwL3.evalAlg (n+2) b
        have key : δ * (U * V) - s i U * s i V * δ =
            (δ * U - s i U * δ) * V + s i U * (δ * V - s i V * δ) := by noncomm_ring
        rw [key, ha, hb, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc, hQ,
          squares_diff_comm i (s i U), mul_assoc, mul_assoc]

/-! ## (R3) and the commutation chain -/

theorem s_fixed_of_commutes (i : Fin (n+1)) (z : SkewPolynomial (n+2)) (hz : z ∈ kernelSubring n)
    (hc : z * generator i.castSucc = generator i.castSucc * z) : s i z = z := by
  have h1 := divided_mul_left i z
  have h2 := divided_left_mul i z
  rw [(mem_kernelSubring z).mp hz i, zero_mul, zero_add, hc] at h1
  rw [(mem_kernelSubring z).mp hz i, mul_zero, sub_zero] at h2
  exact h1.symm.trans h2

theorem next_commutes (i : Fin (n+1)) (z : SkewPolynomial (n+2)) (hz : z ∈ kernelSubring n)
    (hc : z * generator i.castSucc = generator i.castSucc * z) :
    z * generator i.succ = generator i.succ * z := by
  have h := intertwine i z
  rw [s_fixed_of_commutes i z hz hc, (mem_kernelSubring z).mp hz i, mul_zero, sub_eq_zero,
    sub_mul, mul_sub, hc] at h
  exact (sub_right_injective h).symm

/-- An element of `OΛ_N` commuting with all of `OΛ_N` commutes with every variable. -/
theorem commutes_generators (z : SkewPolynomial (n+2)) (hz : z ∈ kernelSubring n)
    (hk : ∀ k ∈ kernelSubring n, k * z = z * k) (j : Fin (n+2)) :
    z * generator j = generator j * z := by
  obtain ⟨k, hk'⟩ := j
  induction k with
  | zero => exact CenterONHRoot.commutes_first_generator n z hk
  | succ k ih =>
      have hi : k < n + 1 := by omega
      have e1 : (⟨k, hi⟩ : Fin (n+1)).castSucc = ⟨k, by omega⟩ := rfl
      have e2 : (⟨k, hi⟩ : Fin (n+1)).succ = ⟨k+1, hk'⟩ := rfl
      have := next_commutes ⟨k, hi⟩ z hz (by rw [e1]; exact ih (by omega))
      rwa [e2] at this

theorem commutes_all_of_generators (z : SkewPolynomial (n+2))
    (hg : ∀ j : Fin (n+2), z * generator j = generator j * z) (p : SkewPolynomial (n+2)) :
    z * p = p * z := by
  obtain ⟨a, rfl⟩ := PbwRealization.Phi_surjective (n+2) p
  induction a using Quotient.inductionOn' with
  | h w =>
    change z * PbwL3.evalAlg (n+2) w = PbwL3.evalAlg (n+2) w * z
    induction w using FreeAlgebra.induction with
    | grade0 r =>
      rw [AlgHom.commutes]
      change z * (r • 1) = (r • 1) * z
      simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    | grade1 j => rw [PbwL3.evalAlg_ι]; exact hg j
    | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb]
    | mul a b ha hb => rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]

/-- (R1) The center of the odd symmetric kernel is its intersection with the center of
the skew polynomial ring. -/
theorem center_kernel (z : kernelSubring n) :
    z ∈ Subring.center (kernelSubring n) ↔
      (z : SkewPolynomial (n+2)) ∈ Subring.center (SkewPolynomial (n+2)) := by
  constructor
  · intro hz
    have hk : ∀ k ∈ kernelSubring n, k * (z : SkewPolynomial (n+2)) = z * k := by
      intro k hkm
      exact congrArg Subtype.val (Subring.mem_center_iff.mp hz ⟨k, hkm⟩)
    apply Subring.mem_center_iff.mpr
    intro p
    exact (commutes_all_of_generators _ (commutes_generators _ z.2 hk) p).symm
  · intro hz
    apply Subring.mem_center_iff.mpr
    intro k
    exact Subtype.ext (Subring.mem_center_iff.mp hz k)

/-- (R3) Elements of `OΛ_N ∩ Z(Pol_N)` are `s_i`-invariant. -/
theorem s_invariant (z : SkewPolynomial (n+2)) (hz : z ∈ kernelSubring n)
    (hc : z ∈ Subring.center (SkewPolynomial (n+2))) (i : Fin (n+1)) : s i z = z :=
  s_fixed_of_commutes i z hz (Subring.mem_center_iff.mp hc _).symm

/-! ## The dot inclusion, all ranks -/

/-- The canonical dot inclusion `Pol_N → ONH_N`, `x_j ↦ dot j`. -/
def polynomialInclusion (n : ℕ) : SkewPolynomial (n+2) →+* Presented n :=
  (NilHeckeBasis.dotMap n).comp (PbwEquivalence.presentedEquiv (n+2)).symm.toRingHom

@[simp] theorem polynomialInclusion_generator (j : Fin (n+2)) :
    polynomialInclusion n (generator j) = dot n j := by
  have he : (PbwEquivalence.presentedEquiv (n+2)).symm (generator j) = PbwL2.q (n+2) j := by
    apply (PbwEquivalence.presentedEquiv (n+2)).injective
    simpa only [RingEquiv.apply_symm_apply, PbwEquivalence.presentedEquiv_apply] using
      (PbwL3.Phi_q (n+2) j).symm
  simp only [polynomialInclusion, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, he, NilHeckeBasis.dotMap_q]

/-- The inclusion acts by LEFT multiplication, on every input. -/
theorem polynomialInclusion_action (p f : SkewPolynomial (n+2)) :
    action n (polynomialInclusion n p) f = p * f := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, add_mul]
  | single a c =>
    change action n (polynomialInclusion n (monomial a c)) f = monomial a c * f
    simp only [polynomialInclusion, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, PbwEquivalence.presentedEquiv_symm_apply,
      PbwEquivalence.lift_monomial, map_zsmul, NilHeckeBasis.dotMap_ordered]
    change c • action n (NilHeckeBasis.dotMonomial a) f = _
    rw [NilHeckeBasis.action_dotMonomial, ← smul_mul_assoc, ← PbwL4.monomial_smul]

theorem polynomialInclusion_injective : Function.Injective (polynomialInclusion n) := by
  intro p q h
  have he := congrArg (fun a : Presented n => action n a 1) h
  simpa only [polynomialInclusion_action, mul_one] using he

/-! ## (R2) The center of the odd nilHecke ring -/

theorem map_mul_of_commutes_dots (F : Module.End ℤ (SkewPolynomial (n+2)))
    (h : ∀ j : Fin (n+2), action n (dot n j) * F = F * action n (dot n j))
    (a f : SkewPolynomial (n+2)) : F (a*f) = a * F f := by
  have hj (j : Fin (n+2)) (b : SkewPolynomial (n+2)) :
      F (generator j * b) = generator j * F b := by
    have he := congrArg (fun T : Module.End ℤ (SkewPolynomial (n+2)) => T b) (h j)
    simpa only [end_mul_apply, action_dot_apply] using he.symm
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) a
  induction x using Quotient.inductionOn' with
  | h w =>
      change F (PbwL3.evalAlg (n+2) w * f) = PbwL3.evalAlg (n+2) w * F f
      induction w using FreeAlgebra.induction generalizing f with
      | grade0 z =>
          rw [AlgHom.commutes]
          change F ((z • 1) * f) = (z • 1) * F f
          simp only [smul_mul_assoc, one_mul, map_smul]
      | grade1 j =>
          rw [PbwL3.evalAlg_ι]
          exact hj j f
      | add u v ihu ihv =>
          rw [map_add, add_mul, map_add, ihu, ihv, add_mul]
      | mul u v ihu ihv =>
          rw [map_mul (PbwL3.evalAlg (n+2)) u v, mul_assoc, ihu, ihv, mul_assoc]

/-- (R2) The center of the presented odd nilHecke ring is the dot image of
`OΛ_N ∩ Z(Pol_N)`. -/
theorem center_nilHecke (a : Presented n) :
    a ∈ Subring.center (Presented n) ↔
      ∃ z ∈ kernelSubring n, z ∈ Subring.center (SkewPolynomial (n+2)) ∧
        a = polynomialInclusion n z := by
  constructor
  · intro ha
    have hcomm : ∀ b : Presented n, b * a = a * b := Subring.mem_center_iff.mp ha
    have hdots : ∀ j : Fin (n+2),
        action n (dot n j) * action n a = action n a * action n (dot n j) := by
      intro j
      have h := congrArg (action n) (hcomm (dot n j))
      rwa [map_mul, map_mul] at h
    have hFmul : ∀ f, action n a f = f * action n a 1 := by
      intro f
      simpa only [mul_one] using map_mul_of_commutes_dots (action n a) hdots f 1
    have hgK : action n a 1 ∈ kernelSubring n := by
      rw [mem_kernelSubring]
      intro i
      have he := congrArg (fun T : Module.End ℤ (SkewPolynomial (n+2)) => T 1)
        (congrArg (action n) (hcomm (crossing n i)))
      simp only [map_mul, end_mul_apply, action_crossing_apply, divided_one,
        map_zero] at he
      exact he
    have hgZ : ∀ k ∈ kernelSubring n, k * action n a 1 = action n a 1 * k := by
      intro k hk
      have h2 := NilHeckeRightKernel.action_right_mul n a k hk 1
      rw [one_mul] at h2
      rw [← hFmul k, h2]
    have hgC : action n a 1 ∈ Subring.center (SkewPolynomial (n+2)) :=
      (center_kernel ⟨action n a 1, hgK⟩).mp
        (Subring.mem_center_iff.mpr (fun k => Subtype.ext (hgZ k.1 k.2)))
    refine ⟨action n a 1, hgK, hgC, ?_⟩
    apply NilHeckeBasis.action_injective n
    apply LinearMap.ext
    intro f
    rw [polynomialInclusion_action, hFmul f]
    exact Subring.mem_center_iff.mp hgC f
  · rintro ⟨z, hzK, hzC, rfl⟩
    apply Subring.mem_center_iff.mpr
    intro b
    apply NilHeckeBasis.action_injective n
    apply LinearMap.ext
    intro f
    simp only [map_mul, end_mul_apply, polynomialInclusion_action]
    rw [← Subring.mem_center_iff.mp hzC f, NilHeckeRightKernel.action_right_mul n b z hzK f]
    exact Subring.mem_center_iff.mp hzC (action n b f)

end
end OddMath.Frontier.CenterONH
