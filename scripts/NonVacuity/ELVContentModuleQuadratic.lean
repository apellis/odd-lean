import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleQuadratic
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I)))
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N rfl
        (content_pair_swap β i j) (contentCrossAffine_mem D (parameterTwist D Sc) i j)) M w
      (BalancedInduction.transformLinear
        (contentAppendTo_supernatural D (parameterTwist D Sc) cutoff N
          (content_pair_swap β i j) rfl (contentCrossAffine_mem D (parameterTwist D Sc) j i)) M w
        (BalancedInduction.tensor
          (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v h m)) =
    BalancedInduction.tensor
      (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j] _ rfl) M.toFunctor v
      (contentAppendToComponent D (parameterTwist D Sc) cutoff N rfl rfl
        (elvSignedPairQuadEval D Sc (R := End ((pres D (parameterTwist D Sc)).obj (ob D [i,j]))) i j
          (dotE D (parameterTwist D Sc) [i,j] 0)
          (dotE D (parameterTwist D Sc) [i,j] 1)) v ≫ h) m :=
  contentInduction_quadratic_tensor D Sc cutoff N β hij M v w h m

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #["ELVModuleRestriction", "ELVModuleInductionTensor",
    "ELVModuleInductionGrading", "ELVModuleInductionMap", "ELVModuleAdjunction",
    "ELVModuleInductionTransform", "ELVModuleInductionRelations", "ELVContentModuleAction",
    "ELVContentModuleTransform", "ELVModuleInductionComp", "ELVParameterUntwist",
    "ELVContentModuleRelations", "ELVContentModuleQuadratic"]
  for suffix in owners do
    let owner := Name.str `OddMath.QuiverHecke.CyclotomicAction suffix
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} declarations in {owner}."
