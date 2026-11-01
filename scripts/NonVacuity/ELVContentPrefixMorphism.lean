import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PrefixMorphismConsumer
open CyclotomicAction.AsymmetricParameters

/-- The full module-morphism comparison on connected asymmetric all-odd data. -/
example := contentInductionCompTo_inner_map datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) [true,false] [false,true]
  (0 + ([true,false] : Multiset Bool)) rfl (by decide)
  [true] (0 + ([true,false,true] : Multiset Bool)) (by decide) rfl (by decide)
  (contentCrossAffine_mem datum scalars true false)
  (vacuumModule datum scalars (fun _ => 12) 12)

example := contentETripleTransform_prefix_cross datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true
  (0 + ([true,false] : Multiset Bool)) (0 + ([true,false,true] : Multiset Bool))
  (by decide) (by decide) rfl (by decide) (by decide)
  (vacuumModule datum scalars (fun _ => 12) 12)

example := contentETripleTransform_prefix_cross datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true true false
  (0 + ([true,true] : Multiset Bool)) (0 + ([true,true,false] : Multiset Bool))
  (by decide) (by decide) rfl (by decide) (by decide)
  (vacuumModule datum scalars (fun _ => 12) 12)

example := contentETripleMap_prefix_cross datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true
  (0 + ([true,false] : Multiset Bool)) (0 + ([true,false,true] : Multiset Bool))
  (by decide) (by decide) rfl (by decide) (by decide)
  (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true,false,true]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true,false,true] : Multiset Bool)))

end OddMath.QuiverHecke.ELVOld.PrefixMorphismConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
