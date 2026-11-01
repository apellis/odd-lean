import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleDots
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ContentCarrierConsumer
open CyclotomicAction.AsymmetricParameters

/-- All-odd connected asymmetric data on the actual vacuum representable. -/
example := contentEPairDot_zero_eq_inner datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false
  (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true,false]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true,false] : Multiset Bool)))

example := contentEPairDot_one_eq_outer datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false
  (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true,false]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true,false] : Multiset Bool)))

example := contentEPair_whiskered_quadratic datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) (i := true) (j := false) (by decide)
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
  (⟨⟨[true,false]⟩, by simp⟩ :
    ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
      (0 + ([true,false] : Multiset Bool)))

example := contentETripleMap_first_dot datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool)) rfl
  (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true,false,true]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true,false,true] : Multiset Bool)))

example := contentETripleMap_middle_dot datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool)) rfl
  (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true,false,true]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true,false,true] : Multiset Bool)))

example := contentETripleMap_last_dot datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false true (0 + ([true,false,true] : Multiset Bool)) rfl
  (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true,false,true]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true,false,true] : Multiset Bool)))

example := contentETriplePolynomial_whiskered datum scalars (fun _ => 12) 12
  (0 : Multiset Bool) true false
  (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
  (⟨⟨[true,false,true]⟩, by simp⟩ :
    ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
      (0 + ([true,false,true] : Multiset Bool)))

example := contentInductionTransform_total datum scalars (fun _ => 12) 12
  (β := (0 : Multiset Bool)) (γ := 0 + ([true] : Multiset Bool))
  rfl rfl (firstDot_parity datum scalars true [])
  (vacuumModule datum scalars (fun _ => 12) 12)
  (⟨⟨[true]⟩, by simp⟩ : ContentCategory datum scalars (fun _ => 12) 12
    (0 + ([true] : Multiset Bool)))

end OddMath.QuiverHecke.ELVOld.ContentCarrierConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleAction,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleTransform,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleRelations,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization,
    `OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleDots] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations of {owner}"
