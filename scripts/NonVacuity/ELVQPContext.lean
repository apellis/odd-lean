import OddMath.QuiverHecke.CyclotomicAction.ELVQPContext
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import NonVacuity.ELVPrefixKilling

noncomputable section
namespace ELVQPContextConsumer
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld MonoidalCategory
open scoped TensorProduct
open CyclotomicAction.AsymmetricParameters

/-- Connected distinct colours, odd moving strand, spectators and arbitrary cutoff. -/
theorem connectedDistinct (N : ℕ) :
    qpEval datum scalars (fun _ => N) true [false, true, false] [true]
      [true, false, true, false, true] (𝟙 _)
      (moveHom datum scalars true [] [false, true, false] ≫
        lastToFirstHom datum scalars true [false, true, false]) =
    qpEval datum scalars (fun _ => N) true [false, true, false] [true]
      [true, false, true, false, true] (𝟙 _)
      (qPoly datum scalars (dotE datum scalars [true, false, true, false] 0)
        (dotE datum scalars [true, false, true, false] 3) true false ≫
        ((moveHom datum scalars true [] [false, true] ≫
          lastToFirstHom datum scalars true [false, true]) ▷
            (pres datum scalars).obj (ob datum [false]))) :=
  qp_distinct datum scalars (fun _ => N) true false (by decide)
    [false, true] [true] [true, false, true, false, true] (𝟙 _)

/-- The continuation is not assumed homogeneous or confined to the affine factor. -/
example (N : ℕ) (h : hom datum scalars (fun _ => N) [true, false, true] [false, true, true]) :=
  qp_distinct datum scalars (fun _ => N) true false (by decide)
    [] [true] [false, true, true] h

/-- Mixed scalar and exterior continuation at a positive even cutoff. -/
example := qp_distinct datum scalars (fun _ => 2) true false (by decide)
  [] [] [true, false]
  (((1 : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) datum (fun _ => 2)) +
      SKM.SYM.elvCoefficientQuotient datum (fun _ => 2)
        (SKM.SYM.delta datum ℚ ⟨true, rfl⟩)) ⊗ₜ[ℚ]
    (𝟙 ((pres datum scalars).obj (ob datum [true, false]))))

example (N : ℕ) := qp_nil datum scalars (fun _ => N) true [false] [true, false] (𝟙 _)

/-- Right-context descent is applied to the full old relation and an ambient continuation. -/
example (N : ℕ) :=
  projection_rightContext_eq datum scalars (fun _ => N) [true] true
    (insert datum scalars (fun _ => N) true [false] [false]
      (relation datum scalars (fun _ => N) false []) ≫ 𝟙 _) 0
    (by simpa only [map_zero] using
      projection_relation datum scalars (fun _ => N) true false [] [true, false] (𝟙 _))
    (𝟙 _)

/-- Empty-prefix induction descends without imposing a moving relation. -/
example := qpEval_of_projection_eq datum scalars (fun _ => 3) true [] [false]
  [true, false] (𝟙 _) (𝟙 _) rfl (𝟙 _)

/-- The same context API includes even colours and the zero cutoff. -/
example := qp_nil (ELVPrefixKillingConsumer.datum 0) (ELVPrefixKillingConsumer.scalars 0)
  (fun _ => 0) () [()] [(), ()] (𝟙 _)

#print axioms qp_distinct
#print axioms relations_rightContext
#print axioms qpEval_of_projection_eq
#print axioms qp_nil
end ELVQPContextConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVQPContext
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory: {owner}"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
