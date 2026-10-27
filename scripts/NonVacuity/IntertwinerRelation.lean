import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRelation
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  for n in #[`OddMath.QuiverHecke.prepend_kernel_tmul_zero,
      `OddMath.QuiverHecke.cyclotomicMk_twist_relation,
      `OddMath.QuiverHecke.append_move_factor,
      `OddMath.QuiverHecke.append_relation_move_tmul_zero,
      `OddMath.QuiverHecke.prefix_relation_move_tmul_zero,
      `OddMath.QuiverHecke.allPrefix_relation_tmul_zero] do
    let axs ← Lean.collectAxioms n
    for a in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains a do
        throwError "Disallowed {a} in {n}"
    logInfo m!"{n}: {axs}"

noncomputable section
open CategoryTheory StringDiagrams Categorification OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace IntertwinerRelationConsumer

def cubic (_ : Bool) : _root_.Polynomial ℚ := Polynomial.X ^ 3
private theorem cubic_parity : CyclotomicPolynomialParity datum cubic := by
  intro i j hj
  by_cases h : 3 = j
  · subst j; simp [cubic]
  · simp [cubic, Polynomial.coeff_X_pow, Ne.symm h] at hj

/-- A repeated odd strand and a distinct spectator, with odd cyclotomic cutoff. -/
example (r : Hn datum scalars 4)
    (b : (qCoefficient datum scalars true (↑[true, false, true] : Multiset Bool)
      cubic cubic_parity 2).toSVec) :=
  allPrefix_relation_tmul_zero datum scalars true [true, false] cubic cubic_parity r b

/-- Minimal prefix: the old word consists only of the repeated colour. -/
example (r : Hn datum scalars 2)
    (b : (qCoefficient datum scalars true {true} cubic cubic_parity 0).toSVec) :=
  allPrefix_relation_tmul_zero datum scalars true [] cubic cubic_parity r b

/-- Arbitrary finite prefixes over arbitrary parity data, including mixed parities. -/
example {I k X : Type} [AddCommGroup X] (D : SKM.Datum I X) [CommRing k]
    (Sc : SKM.Scalars D k) [Fintype I] (i : I) (ν : List I)
    (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
    (r : Hn D Sc (ν.length + 1 + 1))
    (b : (qCoefficient D Sc i (↑(ν ++ [i]) : Multiset I) a ha ν.length).toSVec) :=
  allPrefix_relation_tmul_zero D Sc i ν a ha r b

end IntertwinerRelationConsumer
