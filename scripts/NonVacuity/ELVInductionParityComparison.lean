import OddMath.QuiverHecke.CyclotomicAction.ELVInductionParityComparison
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace InductionParityComparisonConsumer
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (A : C ⥤ D) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  (N : Superfunctor k D (SVec k))
example : (adjunctionParitySourceIso A N).hom ≫
    (adjunctionCounit A).app (supermoduleParityObj N) ≫ (supermoduleParityIso N).hom =
    (adjunctionCounit A).app N := adjunctionParitySourceIso_counit A N
example (w : D) (v : C) (h : A.obj v ⟶ w) (m : N.obj (A.obj v)) :
    (adjunctionParitySourceIso A N).hom.app 1 w
      (tensor A (A ⋙ N.toFunctor) v h m) =
      tensor A (A ⋙ (supermoduleParityObj N).toFunctor) v (twist k 1 h)
        (((restriction A).map (supermoduleParityIso N).inv).app 1 v m) :=
  adjunctionParitySourceIso_tensor A N 1 w v h m
end InductionParityComparisonConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionParityComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
