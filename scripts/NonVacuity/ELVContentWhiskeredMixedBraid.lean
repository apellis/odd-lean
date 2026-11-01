import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskeredMixedBraid
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.WhiskeredMixedBraidConsumer
open CyclotomicAction.AsymmetricParameters

/-- Connected asymmetric all-odd data and the actual vacuum representable.
Every intermediate-content equality is discharged on the concrete words. -/
example :=
  contentWhiskered_mixedBraid datum scalars (fun _ => 12) 12 (0 : Multiset Bool)
    (i := true) (j := false) (by decide)
    ((0 + ([true] : Multiset Bool)) + ([true] : Multiset Bool))
    rfl (by decide) (by decide)
    ((0 + ([true] : Multiset Bool)) + ([false] : Multiset Bool))
    rfl (by decide) (by decide) (by decide)
    (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
    (⟨⟨[true,false,true]⟩, by simp⟩ :
      ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
        (0 + ([true,false,true] : Multiset Bool)))

/-- The other outer colour tests the unequal Cartan exponent. -/
example :=
  contentWhiskered_mixedBraid datum scalars (fun _ => 12) 12 (0 : Multiset Bool)
    (i := false) (j := true) (by decide)
    ((0 + ([false] : Multiset Bool)) + ([false] : Multiset Bool))
    rfl (by decide) (by decide)
    ((0 + ([false] : Multiset Bool)) + ([true] : Multiset Bool))
    rfl (by decide) (by decide) (by decide)
    (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
    (⟨⟨[false,true,false]⟩, by simp⟩ :
      ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
        (0 + ([false,true,false] : Multiset Bool)))
end OddMath.QuiverHecke.ELVOld.WhiskeredMixedBraidConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskeredMixedBraid
  let some idx := env.header.moduleNames.idxOf? target | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
#print axioms OddMath.QuiverHecke.ELVOld.contentWhiskered_mixedBraid

