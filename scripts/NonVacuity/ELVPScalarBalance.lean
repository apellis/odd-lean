import OddMath.QuiverHecke.CyclotomicAction.ELVPScalarBalance
import OddMath.QuiverHecke.CyclotomicAction.ELVQPProduct

noncomputable section
namespace ELVPScalarBalanceConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld ELVPScalar
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Coefficient balance with an arbitrary full-coefficient ambient continuation. -/
theorem withContinuation (i : I) (v w : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (h : hom D Sc cutoff (i :: v) w) :
    ((affineUnit D Sc cutoff (v ++ [i]) (i :: v) (lastToFirstHom D Sc i v) ≫
      ELVOld.relation D Sc cutoff i v) ≫
        insert D Sc cutoff i v v (scalar D Sc cutoff v a)) ≫ h =
    (rightContext D Sc cutoff [i] v v
      (twist k (D.parity i * wordSumParity D v + (cutoff i : ZMod 2) * D.parity i)
        (scalar D Sc cutoff v a)) ≫
      (affineUnit D Sc cutoff (v ++ [i]) (i :: v) (lastToFirstHom D Sc i v) ≫
        ELVOld.relation D Sc cutoff i v)) ≫ h :=
  congrArg (fun f => f ≫ h) (oldGenerator_scalar_balance D Sc cutoff i v a)

#print axioms oldGenerator_scalar_balance
#print axioms elv_comm
#print axioms scalar_slide
end ELVPScalarBalanceConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPScalarBalance
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
