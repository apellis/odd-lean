import OddMath.Frontier.NilHeckeBasis
import OddMath.Frontier.NilHeckeRightKernel

/-! EKL1111.1320v1, Proposition 2.15, pp13–14: literal ordinary-center
statement FALSIFIED at N=3 in BOTH actual rings. The volume is central but
not a polynomial in squared generators. No corrected classification or
supercenter reinterpretation is claimed. Initial controls were checked
before this production module:
D0(x0*x1*x2) = (x1-x1)*x2 = 0;
D1(x0*x1*x2) = -x0*(x2-x2) = 0.
Moving xj past the other two variables gives two minus signs.
Signed swap contributes three minus signs and one reordering minus sign.
Rank two x0*x1 is in the kernel but does not commute with x0. -/
namespace OddMath.Frontier.NilHeckeCenter
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open OddMath.Frontier.AllRankDivided OddMath.Frontier.NilHeckeAction
open OddMath.Frontier.OddSymmetricKernel
noncomputable section

def volume : SkewPolynomial 3 := generator 0 * generator 1 * generator 2

theorem mm {n : ℕ} (a b : Fin n → ℕ) (r t : ℤ) :
    monomial a r * monomial b t = monomial (a+b) (r*t*OddMath.skewSign a b) :=
  OddMath.SkewPolynomial.mul_monomial a b r t

theorem volume_coefficient : volume ![1,1,1] = 1 := by
  simp only [volume, generator, mm]
  norm_num [monomial, expSingle, OddMath.skewSign, OddMath.crossingCount,
    Fin.sum_univ_three, Fin.sum_univ_two, Finset.sum_filter,
    Finsupp.single_apply, Pi.add_apply, Fin.ext_iff]
  funext i
  fin_cases i <;> decide

theorem volume_kernel : volume ∈ kernelSubring 1 := by
  intro i
  fin_cases i <;>
    simp [volume, divided_mul, divided_generator, s_generator, Equiv.swap_apply_def]

theorem volume_commutes_generators (j : Fin 3) :
    volume * generator j = generator j * volume := by
  fin_cases j <;> simp only [volume, generator, mm] <;>
    congr 1 <;>
    norm_num [expSingle, OddMath.skewSign, OddMath.crossingCount,
      Fin.sum_univ_three, Fin.sum_univ_two, Finset.sum_filter,
    Finsupp.single_apply, Pi.add_apply, Fin.ext_iff]
    <;> funext k <;> fin_cases k <;> decide

theorem volume_signed_fixed (i : Fin 2) : s i volume = volume := by
  fin_cases i <;> simp only [volume, map_mul, s_generator] <;>
    norm_num [Equiv.swap_apply_def] <;>
    simp only [neg_mul, mul_neg, neg_neg, generator, mm] <;>
    simp [monomial, expSingle, OddMath.skewSign, OddMath.crossingCount,
      Fin.sum_univ_three, Fin.sum_univ_two, Finset.sum_filter,
    Finsupp.single_apply, Pi.add_apply, Fin.ext_iff]
    <;> congr 1 <;> funext k <;> fin_cases k <;> decide

theorem rankTwo_kernel : generator (0 : Fin 2) * generator 1 ∈ kernelSubring 0 := by
  intro i
  fin_cases i
  simp [divided_mul, divided_generator, s_generator]

theorem rankTwo_not_central :
    (generator (0 : Fin 2) * generator 1) * generator 0 ≠
      generator 0 * (generator 0 * generator 1) := by
  intro h
  have he := congrArg (fun f : SkewPolynomial 2 => f ![2,1]) h
  have ha : expSingle (0 : Fin 2) + expSingle 1 + expSingle 0 = ![2,1] := by
    funext i; fin_cases i <;> decide
  have hb : expSingle (0 : Fin 2) + (expSingle 0 + expSingle 1) = ![2,1] := by
    funext i; fin_cases i <;> decide
  simp only [generator, mm] at he
  norm_num [monomial, expSingle, OddMath.skewSign, OddMath.crossingCount,
    Fin.sum_univ_three, Fin.sum_univ_two, Finset.sum_filter,
    Finsupp.single_apply, Pi.add_apply, Fin.ext_iff] at he
  rw [ha, hb] at he
  norm_num at he

def dotVolume : Presented 1 := dot 1 0 * dot 1 1 * dot 1 2

theorem dotVolume_action (f : SkewPolynomial 3) : action 1 dotVolume f = volume * f := by
  simp [dotVolume, volume, action_mul_apply, action_dot_apply, mul_assoc]

theorem dotVolume_commutes_dots (j : Fin 3) : dotVolume * dot 1 j = dot 1 j * dotVolume := by
  apply OddMath.Frontier.NilHeckeBasis.action_injective 1
  apply LinearMap.ext
  intro f
  simp only [action_mul_apply, dotVolume_action, action_dot_apply]
  simpa only [mul_assoc] using congrArg (fun p : SkewPolynomial 3 => p * f)
    (volume_commutes_generators j)

theorem dotVolume_commutes_crossings (i : Fin 2) :
    dotVolume * crossing 1 i = crossing 1 i * dotVolume := by
  apply OddMath.Frontier.NilHeckeBasis.action_injective 1
  apply LinearMap.ext
  intro f
  simp only [action_mul_apply, dotVolume_action, action_crossing_apply,
    divided_mul, volume_kernel i, volume_signed_fixed, zero_mul, zero_add]


/-- Ordinary centrality on every polynomial, by the genuine quotient/free generation. -/
theorem volume_commutes (p : SkewPolynomial 3) : volume * p = p * volume := by
  obtain ⟨a, rfl⟩ := PbwRealization.Phi_surjective 3 p
  induction a using Quotient.inductionOn' with
  | h w =>
    change volume * PbwL3.evalAlg 3 w = PbwL3.evalAlg 3 w * volume
    induction w using FreeAlgebra.induction with
    | grade0 z =>
      rw [AlgHom.commutes]
      change volume * (z • 1) = (z • 1) * volume
      simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    | grade1 j => rw [PbwL3.evalAlg_ι]; exact volume_commutes_generators j
    | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb]
    | mul a b ha hb =>
      rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]

theorem volume_central : volume ∈ Subring.center (SkewPolynomial 3) :=
  Subring.mem_center_iff.mpr (fun p => (volume_commutes p).symm)

/-- A literal element of the actual divided-difference joint kernel. -/
def kernelVolume : kernelSubring 1 := ⟨volume, volume_kernel⟩

theorem kernelVolume_central : kernelVolume ∈ Subring.center (kernelSubring 1) := by
  apply Subring.mem_center_iff.mpr
  intro p
  apply Subtype.ext
  exact (volume_commutes p.val).symm

/-- Arbitrary quotient elements, not merely all generators. The inherited
right-kernel theorem itself uses free-algebra induction and quotient descent. -/
theorem dotVolume_commutes (a : Presented 1) : dotVolume * a = a * dotVolume := by
  apply NilHeckeBasis.action_injective 1
  apply LinearMap.ext
  intro f
  simp only [action_mul_apply, dotVolume_action]
  rw [volume_commutes f, NilHeckeRightKernel.action_right_mul 1 a volume volume_kernel,
    volume_commutes (action 1 a f)]

theorem dotVolume_central : dotVolume ∈ Subring.center (Presented 1) :=
  Subring.mem_center_iff.mpr (fun a => (dotVolume_commutes a).symm)

/-- Literal integer subring generated by the squared variables; symmetry would
only restrict this set further. This is not defined using the center. -/
def squaredVariableRing : Subring (SkewPolynomial 3) :=
  Subring.closure (Set.range (fun j : Fin 3 => generator j ^ 2))

/-- Auxiliary even-exponent span, used ONLY to exclude squared-variable images. -/
def evenSpan : Submodule ℤ (SkewPolynomial 3) :=
  Submodule.span ℤ (Set.range (fun a : Fin 3 → ℕ => monomial (fun j => 2 * a j) 1))

theorem even_monomial_mem (a : Fin 3 → ℕ) : monomial (fun j => 2 * a j) 1 ∈ evenSpan :=
  Submodule.subset_span ⟨a, rfl⟩

theorem evenSpan_mul {p q : SkewPolynomial 3} (hp : p ∈ evenSpan) (hq : q ∈ evenSpan) :
    p * q ∈ evenSpan := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨a,rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨b,rfl⟩ := hq
      rw [mm]
      have he : (fun j => 2 * a j) + (fun j => 2 * b j) = (fun j => 2 * (a+b) j) := by
        funext j; simp only [Pi.add_apply, Nat.mul_add]
      rw [he]
      simpa only [one_mul, ← PbwL4.monomial_smul] using
        evenSpan.smul_mem (OddMath.skewSign (fun j => 2*a j) (fun j => 2*b j))
          (even_monomial_mem (a+b))
    | zero => simpa only [mul_zero] using evenSpan.zero_mem
    | add p q _ _ hp hq => simpa only [mul_add] using evenSpan.add_mem hp hq
    | smul z p _ hp => simpa only [mul_smul_comm] using evenSpan.smul_mem z hp
  | zero => simpa only [zero_mul] using evenSpan.zero_mem
  | add p q _ _ hp hq => simpa only [add_mul] using evenSpan.add_mem hp hq
  | smul z p _ hp => simpa only [smul_mul_assoc] using evenSpan.smul_mem z hp

def evenSubring : Subring (SkewPolynomial 3) where
  carrier := evenSpan
  zero_mem' := evenSpan.zero_mem
  add_mem' := evenSpan.add_mem
  neg_mem' := evenSpan.neg_mem
  mul_mem' := evenSpan_mul
  one_mem' := by simpa only [mul_zero] using even_monomial_mem 0

theorem square_mem_even (j : Fin 3) : generator j ^ 2 ∈ evenSubring := by
  rw [pow_two]
  change OddMath.SkewPolynomial.mul (generator j) (generator j) ∈ evenSpan
  rw [OddMath.SkewPolynomial.generator_square]
  convert even_monomial_mem (expSingle j) using 2
  funext k
  simp only [Pi.add_apply, two_mul]

theorem squaredVariableRing_le_even : squaredVariableRing ≤ evenSubring := by
  apply Subring.closure_le.mpr
  rintro _ ⟨j,rfl⟩
  exact square_mem_even j

/-- Every coefficient with an odd exponent vanishes, not just a finite test. -/
theorem evenSpan_odd_coefficient {p : SkewPolynomial 3} (hp : p ∈ evenSpan)
    (a : Fin 3 → ℕ) (j : Fin 3) (ha : a j % 2 = 1) : p a = 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b,rfl⟩ := hp
    have hne : (fun k => 2 * b k) ≠ a := by
      intro he
      have hj := congrFun he j
      omega
    simp [monomial, Finsupp.single_apply, hne]
  | zero => rfl
  | add p q _ _ hp hq => simp only [Finsupp.add_apply, hp, hq, add_zero]
  | smul z p _ hp => simp only [Finsupp.smul_apply, hp, smul_zero]

theorem squared_odd_coefficient {p : SkewPolynomial 3} (hp : p ∈ squaredVariableRing)
    (a : Fin 3 → ℕ) (j : Fin 3) (ha : a j % 2 = 1) : p a = 0 :=
  evenSpan_odd_coefficient (squaredVariableRing_le_even hp) a j ha

theorem volume_not_squared : volume ∉ squaredVariableRing := by
  intro h
  have he := squared_odd_coefficient h ![1,1,1] 0 (by decide)
  rw [volume_coefficient] at he
  exact one_ne_zero he

/-- Explicit falsification of the kernel-center assertion of EKL Prop 2.15. -/
theorem kernel_center_counterexample :
    ∃ z : kernelSubring 1, z ∈ Subring.center (kernelSubring 1) ∧
      (z : SkewPolynomial 3) ∉ squaredVariableRing :=
  ⟨kernelVolume, kernelVolume_central, volume_not_squared⟩

/-- Canonical polynomial inclusion into the ACTUAL nilHecke presentation,
using the inherited skew PBW equivalence and the genuine dot quotient map. -/
def polynomialInclusion : SkewPolynomial 3 →+* Presented 1 :=
  (NilHeckeBasis.dotMap 1).comp (PbwEquivalence.presentedEquiv 3).symm.toRingHom

@[simp] theorem polynomialInclusion_generator (j : Fin 3) :
    polynomialInclusion (generator j) = dot 1 j := by
  have he : (PbwEquivalence.presentedEquiv 3).symm (generator j) = PbwL2.q 3 j := by
    apply (PbwEquivalence.presentedEquiv 3).injective
    simpa only [RingEquiv.apply_symm_apply, PbwEquivalence.presentedEquiv_apply] using
      (PbwL3.Phi_q 3 j).symm
  simp only [polynomialInclusion, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, he, NilHeckeBasis.dotMap_q]

/-- The inclusion acts by natural LEFT multiplication, on every input. -/
theorem polynomialInclusion_action (p f : SkewPolynomial 3) :
    action 1 (polynomialInclusion p) f = p * f := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, add_mul]
  | single a c =>
    change action 1 (polynomialInclusion (monomial a c)) f = monomial a c * f
    simp only [polynomialInclusion, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, PbwEquivalence.presentedEquiv_symm_apply,
      PbwEquivalence.lift_monomial, map_zsmul, NilHeckeBasis.dotMap_ordered]
    change c • action 1 (NilHeckeBasis.dotMonomial a) f = _
    rw [NilHeckeBasis.action_dotMonomial, ← smul_mul_assoc, ← PbwL4.monomial_smul]

theorem polynomialInclusion_injective : Function.Injective polynomialInclusion := by
  intro p q h
  have he := congrArg (fun a : Presented 1 => action 1 a 1) h
  simpa only [polynomialInclusion_action, mul_one] using he

@[simp] theorem polynomialInclusion_volume : polynomialInclusion volume = dotVolume := by
  simp only [volume, dotVolume, map_mul, polynomialInclusion_generator]

/-- Explicit exclusion from the canonical squared-polynomial image, not an
abstract matrix-center identification. In fact symmetry is not needed. -/
theorem dotVolume_not_squared_image (p : SkewPolynomial 3) (hp : p ∈ squaredVariableRing) :
    polynomialInclusion p ≠ dotVolume := by
  intro h
  rw [← polynomialInclusion_volume] at h
  exact volume_not_squared (polynomialInclusion_injective h ▸ hp)

/-- The squared-dot subring is defined by the genuine presented generators. -/
def squaredDotRing : Subring (Presented 1) :=
  Subring.closure (Set.range (fun j : Fin 3 => dot 1 j ^ 2))

theorem squaredDotRing_le_image :
    squaredDotRing ≤ squaredVariableRing.map polynomialInclusion := by
  apply Subring.closure_le.mpr
  rintro _ ⟨j,rfl⟩
  exact ⟨generator j ^ 2, Subring.subset_closure ⟨j,rfl⟩,
    by simp only [map_pow, polynomialInclusion_generator]⟩

theorem dotVolume_not_squared : dotVolume ∉ squaredDotRing := by
  intro h
  obtain ⟨p,hp,he⟩ := squaredDotRing_le_image h
  exact dotVolume_not_squared_image p hp he

/-- Explicit falsification of the presented nilHecke-center assertion. -/
theorem nilHecke_center_counterexample :
    ∃ z : Presented 1, z ∈ Subring.center (Presented 1) ∧ z ∉ squaredDotRing :=
  ⟨dotVolume, dotVolume_central, dotVolume_not_squared⟩

/-- The two printed ordinary-center assertions fail in the SAME rank, with
compatible witnesses under the canonical natural left-multiplication map. -/
theorem prop215_counterexample :
    kernelVolume ∈ Subring.center (kernelSubring 1) ∧
    (kernelVolume : SkewPolynomial 3) ∉ squaredVariableRing ∧
    polynomialInclusion (kernelVolume : SkewPolynomial 3) = dotVolume ∧
    dotVolume ∈ Subring.center (Presented 1) ∧ dotVolume ∉ squaredDotRing :=
  ⟨kernelVolume_central, volume_not_squared, polynomialInclusion_volume,
    dotVolume_central, dotVolume_not_squared⟩

end
end OddMath.Frontier.NilHeckeCenter
