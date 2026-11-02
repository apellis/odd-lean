import OddMath.QuiverHecke.HalfTurn.BoundedDetection
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-! Actual reversed first-boundary classes detect bounded source coordinates
at asymmetric odd parameters, even with heavy even and odd coefficients killed.
An occupied odd coefficient/PBW basis vector survives in the quotient.
-/
noncomputable section
namespace NonVacuity.QuiverHeckeHalfTurnBoundedDetection
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def s : List Bool := [false, true]
private def δ (i : Bool) : SKM.SYM D ℚ := SKM.SYM.delta D ℚ ⟨i, rfl⟩
private def e : SKM.SYM D ℚ := SKM.SYM.e D ℚ false 1
private def T : Set (SKM.SYM D ℚ) := {e, δ true * e}

private theorem T_parity : ∀ a ∈ T, ∃ p, CoefParity D p a := by
  rintro a (rfl | rfl)
  · exact ⟨0, coefParity_e D false 1⟩
  · exact ⟨1, (coefParity_delta D ⟨true, rfl⟩).mul D (coefParity_e D false 1)⟩

private theorem T_weight : ∀ a ∈ T, a ∈ SKM.SYM.CoefficientAtLeast D ℚ 4 := by
  have he : e ∈ SKM.SYM.CoefficientAtLeast D ℚ 4 :=
    SKM.SYM.elementary_mem_coefficientAtLeast D ℚ false 1
  rintro a (rfl | rfl)
  · exact he
  · exact SKM.SYM.coefficientAtLeast_antitone D ℚ (by decide : 4 ≤ 1 + 4)
      (SKM.SYM.coefficientAtLeast_mul D ℚ
        (SKM.SYM.delta_mem_coefficientAtLeast D ℚ ⟨true, rfl⟩) he)

/-- Both high coefficient generators have proved parity and actual weight. -/
example : LinearMap.ker (halfTurnBoundaryClass D Sc (fun _ => 6) T s s) =
    TransformedIdeal D Sc (fun _ => 6) T s s :=
  halfTurnBoundaryClass_ker D Sc (fun _ => 6) T T_parity s s

private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D Sc s s 1 =>
      halfTurnBoundaryClass D Sc (fun _ => 6) T s s x.val) :=
  halfTurnBoundaryClass_injective_on_extendedAtMost D Sc T_parity
    (fun _ => by decide : ∀ i : Bool, 4 ≤ (fun _ => 6) i) T_weight (by decide)

/-- The literal reservoir schedule needs no independently assumed kernel. -/
example (μ : Bool → ℤ) :
    Function.Injective (fun x : ExtendedAtMost D Sc s s 1 =>
      halfTurnBoundaryClass D Sc (reservoirLevel D μ s 1) T s s x.val) :=
  halfTurnBoundaryClass_reservoir_injective D Sc μ s s 1 T_parity T_weight

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

/-- Detection is occupied: this full odd coefficient/PBW coordinate is nonzero
in the actual target quotient with both heavy generators imposed. -/
example : halfTurnBoundaryClass D Sc (fun _ => 6) T s s occupied.val ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D Sc s s 1) :=
    bounded_injective (by simpa only [map_zero] using hz)
  exact (extensionBasis D Sc s s).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

end NonVacuity.QuiverHeckeHalfTurnBoundedDetection

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.HalfTurn.BoundedDetection
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
