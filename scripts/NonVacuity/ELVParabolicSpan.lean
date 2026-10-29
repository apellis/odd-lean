import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicSpan

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace ELVParabolicSpanConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- A first-strand output split of any size retains arbitrary full coefficients. -/
example (j : I) (v t : List I) (hN : [j].length + t.length = v.length)
    (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    (shuffleAffineEquiv D Sc cutoff hN).symm (Finsupp.single x a) =
      affineUnit D Sc cutoff _ _ (shPsi D Sc [j].length x.1.1) ≫
        shuffleParabolic D Sc cutoff x a := by
  rw [shuffleAffineEquiv_symm_single, shuffle_parabolic_factorization]

/-- At empty old word the projection kills no affine element. -/
example (i : I) (w : List I) (f : hom D Sc cutoff [i] w) :
    appendProjection D Sc cutoff i [] w f = 0 ↔ f = 0 := by
  rw [appendProjection_eq_zero_iff, appendRelations_nil, Submodule.mem_bot]

/-- The arbitrary-word IS2 reduction uses the prescribed W, not a replacement map. -/
example (i : I) (v w : List I)
    (hS : ∀ (j : I) (t : List I) (hN : [j].length + t.length = (v ++ [i]).length)
      (x : ShIdx hN) (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
      (b : hom D Sc cutoff (j :: t) w),
      (affineUnit D Sc cutoff _ _ (shPsi D Sc [j].length x.1.1) ≫
        shuffleParabolic D Sc cutoff x a) ≫ relation D Sc cutoff j t ≫ b ∈
          appendRelations D Sc cutoff i v w ⊔
            LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v))) :
    ideal D Sc cutoff (v ++ [i]) w ≤ appendRelations D Sc cutoff i v w ⊔
      LinearMap.range (Linear.leftComp k (obj D Sc cutoff w) (appendW D Sc cutoff i v)) :=
  ideal_le_appendRelations_sup_range_of_parabolic_terms D Sc cutoff i v w hS

#print axioms shuffleAffineEquiv
#print axioms shuffle_parabolic_factorization
#print axioms hom_mem_of_shuffle_parabolic
#print axioms appendRelations_nil
#print axioms ideal_le_appendRelations_sup_range_of_parabolic_terms
end ELVParabolicSpanConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVParabolicSpan
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory: {owner}"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
