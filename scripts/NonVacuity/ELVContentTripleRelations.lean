import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleRelations
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
    contentETripleMixedBraid D (parameterTwist D Sc) cutoff N β i j M w =
      contentETriplePolynomial D Sc cutoff N β i j M w :=
  contentETriple_mixedBraid D Sc cutoff N β hij M w

example (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    EvenComparisonAt (k := k) (contentETripleComparison D Sc cutoff N β i j l γ h) M :=
  contentETripleComparison_mem D Sc cutoff N β i j l γ h M

example {β γ : Multiset I} {i j l a b c : I}
    (hσ : β + ([i,j,l] : Multiset I) = γ)
    (hτ : β + ([a,b,c] : Multiset I) = γ) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ((contentETripleTransform D Sc cutoff N hσ hτ hf).app p M).total w =
      contentETripleMap D Sc cutoff N hσ hτ hf M w :=
  contentETripleTransform_total D Sc cutoff N hσ hτ hf M w

example (β : Multiset I) (i j l : I) :
    contentETripleTo D Sc cutoff N β i j l
      (((β + ([i] : Multiset I)) + ([j] : Multiset I)) + ([l] : Multiset I))
      (by rw [add_assoc, add_assoc]; rfl) =
    (contentE D Sc cutoff N β i ⋙ contentE D Sc cutoff N (β + ([i] : Multiset I)) j) ⋙
      contentE D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) l := rfl

#print axioms contentETriple_mixedBraid
#print axioms contentETriple_mixedBraid_tensor
#print axioms contentETripleTransform_total
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleRelations
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
