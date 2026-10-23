import OddMath.CoveringQuantum.Coefficients.HalfSplitting
import OddMath.CoveringQuantum.Negative
import OddMath.CoveringQuantum.PreF.BaseChange
import OddMath.CoveringQuantum.SerreRestrict

/-!
# Nondegeneracy over the generic covering coefficient ring

For every super Cartan datum, the free-form radical equals the Serre
ideal over the actual polynomial quotient `ℚ(q)[π]/(π²-1)`. The form on the
Serre presentation is therefore nondegenerate. For finite index sets the proof
combines the two field specializations with the central-idempotent detection
theorem; arbitrary index sets reduce to finite ones by restriction
(`SuperCartanDatum.serreIdeal_eq_radical_of_finset`).

This establishes the half-algebra nondegeneracy input; it does not construct
the form on the modified full algebra in Brundan–Ellis Theorem 10.1.
-/

noncomputable section
namespace OddMath.CoveringQuantum.Coefficients

variable {I : Type*} [DecidableEq I] (C : SuperCartanDatum I)

/-- Specialization of a generic radical vector lies in the specialized radical. -/
theorem specialize_mem_radical (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) {x : PreF Ring I}
    (hx : x ∈ PreF.radical (C.chi q pi) (C.norm q pi)) :
    FreeAlgebra.mapCoeffs (specialize ε hε).toRingHom x ∈
      PreF.radical (C.chi (Units.map (specialize ε hε).toMonoidHom q) ε)
        (C.norm (Units.map (specialize ε hε).toMonoidHom q) ε) := by
  apply PreF.mapCoeffs_mem_radical (specialize ε hε).toRingHom _ _ _ _ _ _ hx
  · intro i j
    simpa using C.map_chi (specialize ε hε).toRingHom q pi i j
  · intro i
    simpa using C.map_norm (specialize ε hε).toRingHom q pi i (denominator_isUnit C i)

private theorem specialize_q_transcendental (ε : RatFunc ℚ) (hε : ε ^ 2 = 1) :
    Transcendental ℚ ((Units.map (specialize ε hε).toMonoidHom q : (RatFunc ℚ)ˣ) : RatFunc ℚ) := by
  change Transcendental ℚ (specialize ε hε (q : Ring))
  rw [specialize_q]
  have hi : (RatFunc.instAlgebraOfPolynomial ℚ ℚ : Algebra ℚ (RatFunc ℚ)) =
      (DivisionRing.toRatAlgebra : Algebra ℚ (RatFunc ℚ)) :=
    Subsingleton.elim _ _
  exact (congrArg (fun a : Algebra ℚ (RatFunc ℚ) ↦
    @Transcendental ℚ (RatFunc ℚ) _ _ a RatFunc.X) hi).mp
      (RatFunc.transcendental_X (K := ℚ))

private theorem serreIdeal_eq_radical_of_finite [Finite I] :
    C.serreIdeal q pi = PreF.radical (C.chi q pi) (C.norm q pi) := by
  apply le_antisymm (C.serreIdeal_le_radical q pi pi_sq)
  intro x hx
  apply (mem_serreIdeal_iff_specialize C x).mpr
  constructor
  · rw [C.serreIdeal_one_eq_radical _ (specialize_q_transcendental 1 (one_pow 2))]
    exact specialize_mem_radical C 1 (one_pow 2) hx
  · rw [C.serreIdeal_neg_one_eq_radical_of_transcendental
      (specialize_q_transcendental (-1) (by norm_num))]
    exact specialize_mem_radical C (-1) (by norm_num) hx

/-- The generic covering form radical is exactly the two-sided Serre ideal. -/
theorem serreIdeal_eq_radical :
    C.serreIdeal q pi = PreF.radical (C.chi q pi) (C.norm q pi) :=
  C.serreIdeal_eq_radical_of_finset q pi pi_sq fun _ ↦
    serreIdeal_eq_radical_of_finite _

/-- Nondegeneracy of the Serre-presented half covering quantum group over
`ℚ(q)[π]/(π²-1)`. -/
theorem serreForm_nondegenerate : (C.serreForm q pi pi_sq).Nondegenerate :=
  (C.serreForm_nondegenerate_iff_ideal_eq q pi pi_sq).mpr (serreIdeal_eq_radical C)

end OddMath.CoveringQuantum.Coefficients
