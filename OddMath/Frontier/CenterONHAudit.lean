import OddMath.Frontier.CenterONH

/-!
# Audit for `CenterONH`

Headline theorems restated with no residual hypothesis, for every `n` (`N = n + 2`),
followed by `#print axioms` for every headline and supporting lemma, and a rank-three
consistency check against the inherited counterexample module `NilHeckeCenter`.
-/

namespace OddMath.Frontier.CenterONHAudit
open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.AllRankDivided OddMath.Frontier.OddSymmetricKernel
open OddMath.Frontier.NilHeckeAction

/-- (R1), restated. -/
theorem center_kernel_restated (n : ℕ) (z : kernelSubring n) :
    z ∈ Subring.center (kernelSubring n) ↔
      (z : SkewPolynomial (n+2)) ∈ Subring.center (SkewPolynomial (n+2)) :=
  CenterONH.center_kernel z

/-- (R2), restated. -/
theorem center_nilHecke_restated (n : ℕ) (a : Presented n) :
    a ∈ Subring.center (Presented n) ↔
      ∃ z ∈ kernelSubring n, z ∈ Subring.center (SkewPolynomial (n+2)) ∧
        a = CenterONH.polynomialInclusion n z :=
  CenterONH.center_nilHecke a

/-- (R3), restated. -/
theorem s_invariant_restated (n : ℕ) (z : SkewPolynomial (n+2)) (hz : z ∈ kernelSubring n)
    (hc : z ∈ Subring.center (SkewPolynomial (n+2))) (i : Fin (n+1)) : s i z = z :=
  CenterONH.s_invariant z hz hc i

/-- The inclusion is injective and acts by left multiplication, all ranks. -/
theorem polynomialInclusion_facts (n : ℕ) :
    Function.Injective (CenterONH.polynomialInclusion n) ∧
      ∀ p f : SkewPolynomial (n+2), action n (CenterONH.polynomialInclusion n p) f = p * f :=
  ⟨CenterONH.polynomialInclusion_injective, CenterONH.polynomialInclusion_action⟩

/-! Rank-three consistency with the inherited module (not used by the proofs). -/

example : (NilHeckeCenter.volume : SkewPolynomial 3) ∈ Subring.center (SkewPolynomial 3) :=
  (CenterONH.center_kernel NilHeckeCenter.kernelVolume).mp NilHeckeCenter.kernelVolume_central

example : CenterONH.polynomialInclusion 1 NilHeckeCenter.volume = NilHeckeCenter.dotVolume := by
  simp only [NilHeckeCenter.volume, NilHeckeCenter.dotVolume, map_mul,
    CenterONH.polynomialInclusion_generator]

example : NilHeckeCenter.dotVolume ∈ Subring.center (Presented 1) :=
  (CenterONH.center_nilHecke _).mpr ⟨NilHeckeCenter.volume, NilHeckeCenter.volume_kernel,
    NilHeckeCenter.volume_central, by
      simp only [NilHeckeCenter.volume, NilHeckeCenter.dotVolume, map_mul,
        CenterONH.polynomialInclusion_generator]⟩

end OddMath.Frontier.CenterONHAudit

#print axioms OddMath.Frontier.CenterONH.center_kernel
#print axioms OddMath.Frontier.CenterONH.center_nilHecke
#print axioms OddMath.Frontier.CenterONH.s_invariant
#print axioms OddMath.Frontier.CenterONH.polynomialInclusion_injective
#print axioms OddMath.Frontier.CenterONH.polynomialInclusion_action
#print axioms OddMath.Frontier.CenterONH.intertwine
#print axioms OddMath.Frontier.CenterONH.commutes_generators
#print axioms OddMath.Frontier.CenterONHRoot.rootRelation
#print axioms OddMath.Frontier.CenterONHRoot.mul_ne_zero'
#print axioms OddMath.Frontier.CenterONHRoot.commutes_first_generator
#print axioms OddMath.Frontier.CenterONHAudit.center_kernel_restated
#print axioms OddMath.Frontier.CenterONHAudit.center_nilHecke_restated
#print axioms OddMath.Frontier.CenterONHAudit.s_invariant_restated
#print axioms OddMath.Frontier.CenterONHAudit.polynomialInclusion_facts
