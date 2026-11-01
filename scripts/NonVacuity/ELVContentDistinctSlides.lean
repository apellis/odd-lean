import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.DistinctSlidesConsumer
open CyclotomicAction.AsymmetricParameters

/-- The connected asymmetric all-odd datum has a nontrivial Koszul slide sign.
The module is the actual vacuum representable, not a supplied action. -/
example :=
  contentEPair_distinct_slide_left datum scalars (fun _ => 12) 12
    (0 : Multiset Bool) (i := false) (j := true) (by decide)
    (0 + ([false,true] : Multiset Bool)) rfl (by decide)
    (vacuumModule datum scalars (fun _ => 12) 12)
    (⟨⟨[false,true]⟩, by simp⟩ :
      ContentCategory datum scalars (fun _ => 12) 12
        (0 + ([false,true] : Multiset Bool)))

example :=
  contentEPair_distinct_slide_right datum scalars (fun _ => 12) 12
    (0 : Multiset Bool) (i := true) (j := false) (by decide)
    (0 + ([true,false] : Multiset Bool)) rfl (by decide)
    (vacuumModule datum scalars (fun _ => 12) 12)
    (⟨⟨[true,false]⟩, by simp⟩ :
      ContentCategory datum scalars (fun _ => 12) 12
        (0 + ([true,false] : Multiset Bool)))
end OddMath.QuiverHecke.ELVOld.DistinctSlidesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctSlides
  let some idx := env.header.moduleNames.idxOf? target | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
#print axioms OddMath.QuiverHecke.ELVOld.contentEPair_distinct_slide_left
#print axioms OddMath.QuiverHecke.ELVOld.contentEPair_distinct_slide_right
