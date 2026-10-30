import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction
import NonVacuity.ELVModuleRestriction
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace ELVModuleAdjunctionConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (σ : List I)

example : (moduleInduction D Sc cutoff N σ).Additive := inferInstance
example : (moduleInduction D Sc cutoff N σ).Linear k := inferInstance
example : IsSuperfunctor k (moduleInduction D Sc cutoff N σ) := inferInstance
example : moduleInduction D Sc cutoff N σ ⊣ moduleRestriction D Sc cutoff N σ :=
  moduleAdjunction D Sc cutoff N σ

example (M : TruncatedModules D Sc cutoff N) :
    (moduleInduction D Sc cutoff N σ).map ((moduleAdjunction D Sc cutoff N σ).unit.app M) ≫
      (moduleAdjunction D Sc cutoff N σ).counit.app ((moduleInduction D Sc cutoff N σ).obj M) =
      𝟙 ((moduleInduction D Sc cutoff N σ).obj M) :=
  (moduleAdjunction D Sc cutoff N σ).left_triangle_components M

example (M L : TruncatedModules D Sc cutoff N) (f : M ⟶ L) :
    f ≫ (moduleAdjunction D Sc cutoff N σ).unit.app L =
      (moduleAdjunction D Sc cutoff N σ).unit.app M ≫
        (moduleRestriction D Sc cutoff N σ).map ((moduleInduction D Sc cutoff N σ).map f) :=
  (moduleAdjunction D Sc cutoff N σ).unit.naturality f

example (M : TruncatedModules D Sc cutoff N) :
    (moduleAdjunction D Sc cutoff N σ).unit.app M ∈
      parity (R := k) M
        ((moduleRestriction D Sc cutoff N σ).obj ((moduleInduction D Sc cutoff N σ).obj M)) 0 :=
  BalancedInduction.adjunctionUnit_mem (truncatedAppend D Sc cutoff N σ) M

end ELVModuleAdjunctionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVModuleRestriction,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTensor,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionGrading,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionMap,
    `OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction]
  let mut counts : Array Nat := owners.map (fun _ => 0)
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if let some j := owners.idxOf? modules[idx.toNat]! then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        counts := counts.modify j (· + 1)
  for i in [:owners.size] do
    if counts[i]! == 0 then throwError "No owned declarations audited for {owners[i]!}"
    logInfo m!"Audited {counts[i]!} declarations in {owners[i]!}."
