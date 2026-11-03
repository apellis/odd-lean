import OddMath.Algebra.SupermoduleIsoOfBijectiveTotals
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace BijectiveTotalsConsumer
universe u
private theorem iso_bijective {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) :
    Function.Bijective (e.hom.total w) := (moduleIsoLinearEquiv e w).bijective

private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private theorem even : (Iso.refl M).hom ∈ parity (R := ℚ) _ _ 0 := id_mem M
private theorem odd : (supermoduleParityIso M).hom ∈ parity (R := ℚ) _ _ 1 :=
  supermoduleParityIso_hom_mem M

example := HomogeneousSuperfunctorIso.ofBijectiveTotals (Iso.refl M).hom even (iso_bijective (Iso.refl M))
example := HomogeneousSuperfunctorIso.ofBijectiveTotals_hom (Iso.refl M).hom even (iso_bijective (Iso.refl M))
example := HomogeneousSuperfunctorIso.ofBijectiveTotals_inv_mem (Iso.refl M).hom even (iso_bijective (Iso.refl M))
example := HomogeneousSuperfunctorIso.ofBijectiveTotals (supermoduleParityIso M).hom odd (iso_bijective (supermoduleParityIso M))
example := HomogeneousSuperfunctorIso.ofBijectiveTotals_hom (supermoduleParityIso M).hom odd (iso_bijective (supermoduleParityIso M))
example := HomogeneousSuperfunctorIso.ofBijectiveTotals_inv_mem (supermoduleParityIso M).hom odd (iso_bijective (supermoduleParityIso M))
example := HomogeneousSuperfunctorIso.ofBijectiveTotals_hom_inv_id (supermoduleParityIso M).hom odd (iso_bijective (supermoduleParityIso M))
example := HomogeneousSuperfunctorIso.ofBijectiveTotals_inv_hom_id (supermoduleParityIso M).hom odd (iso_bijective (supermoduleParityIso M))
end BijectiveTotalsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.Algebra.SupermoduleIsoOfBijectiveTotals
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
