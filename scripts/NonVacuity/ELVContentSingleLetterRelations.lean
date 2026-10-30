import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j] : Multiset I))) :
    (contentEPairCross D (parameterTwist D Sc) cutoff N β i j _ rfl
        (content_pair_swap β i j) M w).comp
      (contentEPairCross D (parameterTwist D Sc) cutoff N β j i _
        (content_pair_swap β i j) rfl M w) =
      contentEPairPolynomial D Sc cutoff N β i j M w :=
  contentEPair_quadratic D Sc cutoff N β hij M w

example (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ((contentEPairCrossTransform D Sc cutoff N β i j γ hij hji).app
      (D.parity i * D.parity j) M).total w = contentEPairCross D Sc cutoff N β i j γ hij hji M w :=
  contentEPairCross_total D Sc cutoff N β i j γ hij hji M w

example (β : Multiset I) (i j : I) :
    contentEPairTo D Sc cutoff N β i j ((β + ([i] : Multiset I)) + ([j] : Multiset I))
      (by rw [add_assoc]; rfl) =
    contentE D Sc cutoff N β i ⋙ contentE D Sc cutoff N (β + ([i] : Multiset I)) j := rfl

#print contentEPair_quadratic
#print axioms contentEPair_quadratic
#print axioms contentEPairCross_total
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
