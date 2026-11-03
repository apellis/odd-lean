import OddMath.QuiverHecke.HalfTurn.OldQuotient
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-! Full-coefficient signed reversal and occupied bounded detection in actual
old category Homs, including the literal elementary-power preimage.
-/
noncomputable section
namespace NonVacuity.QuiverHeckeHalfTurnOldQuotient
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def s : List Bool := [false, true]
private def cutoff (_ : Bool) : ℕ := 6

example : LinearMap.ker (halfTurnOldHom D Sc cutoff s s) =
    TransformedIdeal D Sc cutoff ∅ s s := halfTurnOldHom_ker D Sc cutoff s s

/-- The actual target retains the reversed/twisted old category endpoints. -/
example (x : coefficientObj D Sc s ⟶ coefficientObj D Sc s) :
    (⟨s.reverse⟩ : ELVOld.OldCategory D (parameterTwist D Sc) cutoff) ⟶ ⟨s.reverse⟩ :=
  halfTurnOldHom D Sc cutoff s s x

example {p q : ZMod 2} {x y : coefficientObj D Sc s ⟶ coefficientObj D Sc s}
    (hx : x ∈ parity (R := ℚ) _ _ p) (hy : y ∈ parity (R := ℚ) _ _ q) :=
  halfTurnOldHom_comp D Sc cutoff hx hy

/-- Detection uses the prescribed reservoir schedule, with no kernel premise. -/
example (μ : Bool → ℤ) := halfTurnOldHom_reservoir_injective D Sc μ s s 1

private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D Sc s s 1 =>
      halfTurnOldHom D Sc cutoff s s x.val) :=
  halfTurnOldHom_injective_on_extendedAtMost D Sc cutoff
    (fun _ => (by decide : 4 ≤ 6)) (by decide)

private def identityNF : NFIdx s s := by
  have hc : Categorification.TypeA.canWord s.length (1 : Equiv.Perm (Fin s.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]

private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩})

private def occupied : ExtendedAtMost D Sc s s 1 :=
  ⟨extensionBasis D Sc s s (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩


/-- An occupied odd coefficient/PBW coordinate survives in the actual
first-boundary old category Hom at the twisted parameters. -/
example : halfTurnOldHom D Sc cutoff s s occupied.val ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D Sc s s 1) := by
    apply bounded_injective
    change halfTurnOldHom D Sc cutoff s s occupied.val = halfTurnOldHom D Sc cutoff s s 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D Sc s s).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

/-- The same reversal pulls back the actual elementary powers, unchanged in
exponent, together with the actual old first-boundary ideal. -/
example := halfTurn_oldElementaryPowers_preimage D Sc cutoff (fun _ => 3) s s

end NonVacuity.QuiverHeckeHalfTurnOldQuotient

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.HalfTurn.OldQuotient
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
