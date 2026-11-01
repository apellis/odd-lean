import OddMath.QuiverHecke.CyclotomicAction.ELVContentUncorrectedBraid
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.UncorrectedBraidConsumer
open CyclotomicAction.AsymmetricParameters

/-- All three odd colours equal, on the actual vacuum representable. -/
example :=
  contentWhiskered_braid datum scalars (fun _ => 12) 12 (0 : Multiset Bool)
    true true true (by simp) (0 + ([true,true,true] : Multiset Bool))
    rfl rfl rfl rfl rfl rfl
    (vacuumModule datum scalars (fun _ => 12) 12)
    (⟨⟨[true,true,true]⟩, by simp⟩ :
      ContentCategory datum scalars (fun _ => 12) 12
        (0 + ([true,true,true] : Multiset Bool)))

/-- Adjacent repeated odd colour in the connected asymmetric datum. -/
example :=
  contentWhiskered_braid datum scalars (fun _ => 12) 12 (0 : Multiset Bool)
    true true false (by decide) (0 + ([true,true,false] : Multiset Bool))
    rfl rfl (by decide) (by decide) (by decide) (by decide)
    (vacuumModule datum scalars (fun _ => 12) 12)
    (⟨⟨[true,true,false]⟩, by simp⟩ :
      ContentCategory datum scalars (fun _ => 12) 12
        (0 + ([true,true,false] : Multiset Bool)))
end OddMath.QuiverHecke.ELVOld.UncorrectedBraidConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `OddMath.QuiverHecke.CyclotomicAction.ELVContentUncorrectedBraid
  let some idx := env.header.moduleNames.idxOf? target | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
#print axioms OddMath.QuiverHecke.ELVOld.contentWhiskered_braid
