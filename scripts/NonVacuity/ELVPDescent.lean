import OddMath.QuiverHecke.CyclotomicAction.ELVPDescent

noncomputable section
namespace ELVPDescentConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- An arbitrary old composite followed by an ambient continuation is balanced. -/
theorem compositeBalance (i : I) (v t u w : List I)
    (f : hom D Sc cutoff v t) (g : hom D Sc cutoff t u)
    (h : hom D Sc cutoff (i :: u) w) :
    appendProjection D Sc cutoff i v w
      ((rightContext D Sc cutoff [i] v u (f ≫ g) ≫ ELVOld.appendW D Sc cutoff i u) ≫ h) =
    appendProjection D Sc cutoff i v w
      ((ELVOld.appendW D Sc cutoff i v ≫ insert D Sc cutoff i v u
        (twist k (ELVOld.appendQ D cutoff i v) (f ≫ g))) ≫ h) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← Preadditive.sub_comp]
  exact (appendProjection_eq_zero_iff D Sc cutoff i v w _).mpr
    (appendRelations_comp D Sc cutoff i
      (appendError_mem_appendRelations D Sc cutoff i (f ≫ g)) h)

/-- An arbitrary representative is sent by the prescribed W, over every commutative base. -/
theorem prescribedMap (i : I) (v w : List I) (h : hom D Sc cutoff (i :: v) w) :
    pMap D Sc cutoff i v w (projection D Sc cutoff i v w h) =
      appendProjection D Sc cutoff i v w
        ((affineUnit D Sc cutoff (v ++ [i]) (i :: v) (lastToFirstHom D Sc i v) ≫
          relation D Sc cutoff i v) ≫ h) := pMap_projection D Sc cutoff i v w h

#print axioms ELVOld.appendError_lastDot_mem
#print axioms ELVOld.appendError_crossLast_mem
#print axioms ELVOld.appendError_mem_appendRelations
#print axioms ELVOld.pMap
#print axioms ELVOld.pMap_projection
end ELVPDescentConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVAppendRelations,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendBalance,
      `OddMath.QuiverHecke.CyclotomicAction.ELVPDescent] do
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
