import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) (σ τ : List I)
    (γ : Multiset I) (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.mapComponent (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
        (BalancedInduction.transformComponent
          (contentAppendTo_supernatural D Sc cutoff N rfl rfl ha) M) p z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' h'
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap :=
  contentInductionComp_inner D Sc cutoff N β σ τ γ h h' ha M z

example (β : Multiset I) (σ τ : List I)
    (γ : Multiset I) (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : End ((pres D Sc).obj (ob D τ))}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h h ha)
        (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ _ rfl) M) z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' h'
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap :=
  contentInductionComp_outer D Sc cutoff N β σ τ γ h h' ha M z


#print axioms contentInductionComp_inner
#print axioms contentInductionComp_outer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskering
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
