import OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositeComparison
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) (i j : I) :
    contentE D Sc cutoff N β i ⋙ contentE D Sc cutoff N (β + ([i] : Multiset I)) j ≅
      contentInductionTo D Sc cutoff N β [i,j]
        ((β + ([i] : Multiset I)) + ([j] : Multiset I))
        (by rw [add_assoc]; rfl) :=
  contentEPairComparison D Sc cutoff N β i j

example (β : Multiset I) (i j : I) (M : ContentModules D Sc cutoff N β) :
    EvenComparisonAt (k := k) (contentEPairComparison D Sc cutoff N β i j) M :=
  contentInductionComp_mem D Sc cutoff N β [i] [j] _ rfl _ M

example (β : Multiset I) (σ τ : List I) (γ : Multiset I)
    (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {M L : ContentModules D Sc cutoff N β} (f : M ⟶ L) :
    (contentInductionTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h).map
        ((contentInduction D Sc cutoff N β σ).map f) ≫
        (contentInductionComp D Sc cutoff N β σ τ γ h h').hom.app L =
      (contentInductionComp D Sc cutoff N β σ τ γ h h').hom.app M ≫
        (contentInductionTo D Sc cutoff N β (σ ++ τ) γ h').map f :=
  contentInductionComp_naturality D Sc cutoff N β σ τ γ h h' f

example (β : Multiset I) (σ τ : List I)
    (γ : Multiset I) (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (z : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h).obj w ⟶ z)
    (a : (contentAppend D Sc cutoff N β σ).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionComp D Sc cutoff N β σ τ γ h h').hom.app M).total z
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
        (BalancedInduction.induced (contentAppend D Sc cutoff N β σ) M).toFunctor w g
        (BalancedInduction.tensor (contentAppend D Sc cutoff N β σ) M.toFunctor v a m)) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h') M.toFunctor v
      (eqToHom (congrArg (fun F => F.obj v)
        (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')).symm ≫
        (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h).map a ≫ g) m := by
  apply contentInductionComp_hom_total_tensor

#print axioms contentInductionComp_hom_total_tensor
#print axioms contentEPairComparison
#print axioms contentInductionComp_mem
#print axioms contentInductionComp_naturality
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositeComparison
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
