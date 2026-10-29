import OddMath.QuiverHecke.CyclotomicAction.ELVQDescent

noncomputable section
namespace ELVQDescentConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Q kills a right-extended arbitrary old ideal element and continuation. -/
theorem oldRelation (i : I) (v t w : List I) (r : hom D Sc cutoff v t)
    (hr : r ∈ ideal D Sc cutoff v t) (a : hom D Sc cutoff (t ++ [i]) w) :
    projection D Sc cutoff i v w
      (move D Sc cutoff i v ≫ (rightContext D Sc cutoff [i] v t r ≫ a)) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (move_appendRelations D Sc cutoff i (appendRelations_mem D Sc cutoff i hr a))

/-- On every quotient class the two prescribed maps recover the signed polynomial. -/
theorem quotientComposite (i : I) (v w : List I) (x : Target D Sc cutoff i v w) :
    qMap D Sc cutoff i v w (pMap D Sc cutoff i v w x) = signedQPMap D Sc cutoff i v w x :=
  LinearMap.congr_fun (qMap_comp_pMap D Sc cutoff i v w) x

/-- The even repeated-colour normalization has not been replaced by +1. -/
theorem repeatedEven (i : I) (hi : D.parity i = 0) (v : List I) (b : ℕ) :
    qpFactor D Sc i v i b = -1 := by simp [qpFactor, hi]

#print axioms ELVOld.move_comp_rightContext
#print axioms ELVOld.move_appendRelations
#print axioms ELVOld.qMap
#print axioms ELVOld.qMap_comp_pMap
end ELVQDescentConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVQDescent
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if env.getModuleIdxFor? name == some idx then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
  if count == 0 then throwError "Empty declaration inventory: {owner}"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
