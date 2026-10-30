import OddMath.QuiverHecke.CyclotomicAction.ELVContentMixedPolynomial
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentMixedBraid D (parameterTwist D Sc) cutoff N β i j M w =
      contentMixedBraidPolynomial D Sc cutoff N β i j M w :=
  contentMixedBraid_polynomial_linear D Sc cutoff N β hij M w

#print contentMixedBraid_polynomial_linear
#print axioms contentMixedBraid_polynomial_linear
#print axioms contentInduction_three_powers
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for suffix in #["ELVContentMixedBraid", "ELVContentMixedPolynomial"] do
    let owner := Name.str `OddMath.QuiverHecke.CyclotomicAction suffix
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} declarations in {owner}."
