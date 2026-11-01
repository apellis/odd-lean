import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskeredMixedBraid
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

example (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (z : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentWhiskeredPathIij D (parameterTwist D Sc) cutoff N β i j M z -
        contentWhiskeredPathJii D (parameterTwist D Sc) cutoff N β i j M z =
      contentWhiskeredPolynomial D Sc cutoff N β i j M z :=
  contentWhiskered_mixedBraid D Sc cutoff N β hij M z

namespace WhiskeredMixedBraidConsumer
open CyclotomicAction.AsymmetricParameters

/-- Connected asymmetric all-odd datum, with its actual coefficient-truncated
vacuum representable and a literal three-strand target. Neither a zero module
nor an assumed action or braid proof is supplied. -/
example :=
  contentWhiskered_mixedBraid datum scalars (fun _ => 12) 12 (0 : Multiset Bool)
    (i := true) (j := false) (by decide)
    (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
    (⟨⟨[true, false, true]⟩, by simp⟩ :
      ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
        (0 + ([true, false, true] : Multiset Bool)))

/-- Reverse the outside colour: this tests the other asymmetric Cartan entry. -/
example :=
  contentWhiskered_mixedBraid datum scalars (fun _ => 12) 12 (0 : Multiset Bool)
    (i := false) (j := true) (by decide)
    (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
    (⟨⟨[false, true, false]⟩, by simp⟩ :
      ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
        (0 + ([false, true, false] : Multiset Bool)))
end WhiskeredMixedBraidConsumer

end OddMath.QuiverHecke.ELVOld

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
