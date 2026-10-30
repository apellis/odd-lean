import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform
import NonVacuity.ELVModuleAdjunction
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace ELVModuleInductionTransformConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (i j : I) : SuperNatTrans k (moduleInduction D Sc cutoff N [j, i])
    (moduleInduction D Sc cutoff N [i, j]) := moduleInductionCross D Sc cutoff N i j

example (i : I) (M L : TruncatedModules D Sc cutoff N) {q : ZMod 2}
    (f : M ⟶ L) (hf : f ∈ parity (R := k) M L q) :
    (moduleInduction D Sc cutoff N [i]).map f ≫
        (moduleInductionDot D Sc cutoff N i).app (D.parity i) L =
      sign k (D.parity i * q) •
        ((moduleInductionDot D Sc cutoff N i).app (D.parity i) M ≫
          (moduleInduction D Sc cutoff N [i]).map f) :=
  ((moduleInductionDot D Sc cutoff N i).isSupernatural (D.parity i)).naturality hf

example (i j : I) (M : TruncatedModules D Sc cutoff N)
    (w v : TruncatedCategory D Sc cutoff N)
    (h : (truncatedAppend D Sc cutoff N [j, i]).obj v ⟶ w) (m : M.obj v) :
    ((moduleInductionCross D Sc cutoff N i j).app (D.parity i * D.parity j) M).app
      (D.parity i * D.parity j) w
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [j, i]) M.toFunctor v h m) =
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i, j]) M.toFunctor v
      (truncatedAppendComponent D Sc cutoff N (crossTwo D Sc i j) v ≫
        twist k (D.parity i * D.parity j) h) m :=
  moduleInductionCross_tensor D Sc cutoff N i j M w v h m

example (i : I) (M : TruncatedModules D Sc cutoff N)
    (w v : TruncatedCategory D Sc cutoff N)
    (h : (truncatedAppend D Sc cutoff N [i]).obj v ⟶ w) (m : M.obj v) :
    ((moduleInductionDot D Sc cutoff N i).app (D.parity i) M).app (D.parity i) w
      (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor v h m) =
    BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor v
      (truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0) v ≫
        twist k (D.parity i) h) m :=
  moduleInductionDot_tensor D Sc cutoff N i M w v h m

end ELVModuleInductionTransformConsumer

#print axioms BalancedInduction.transform
#print axioms BalancedInduction.transformComponent_supernatural
#print axioms BalancedInduction.transform_unit
#print axioms BalancedInduction.transform_counit
#print axioms moduleInductionDot_tensor
#print axioms moduleInductionCross_tensor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations audited"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
