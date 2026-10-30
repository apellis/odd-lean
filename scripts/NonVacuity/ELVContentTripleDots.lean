import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleDots
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem importing_triple_first_dot (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h h (firstDot_parity D Sc i [j,l]) M z =
      contentWhiskeredFirstDot D Sc cutoff N β i j l γ h M z :=
  contentETripleMap_first_dot D Sc cutoff N β i j l γ h M z

theorem importing_triple_middle_dot (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h h
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
        (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D [l]))
          (firstDot_parity D Sc j []))) M z =
      contentWhiskeredMiddleDot D Sc cutoff N β i j l γ h M z :=
  contentETripleMap_middle_dot D Sc cutoff N β i j l γ h M z

theorem importing_triple_last_dot (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h h
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [j]))
          (firstDot_parity D Sc l []))) M z =
      contentWhiskeredLastDot D Sc cutoff N β i j l γ h M z :=
  contentETripleMap_last_dot D Sc cutoff N β i j l γ h M z
end OddMath.QuiverHecke.ELVOld

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := `OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleDots
  let some idx := env.header.moduleNames.idxOf? target | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned inventory"
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
#print axioms OddMath.QuiverHecke.ELVOld.importing_triple_first_dot
#print axioms OddMath.QuiverHecke.ELVOld.importing_triple_middle_dot
#print axioms OddMath.QuiverHecke.ELVOld.importing_triple_last_dot
