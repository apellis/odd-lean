import OddMath.QuiverHecke.CyclotomicAction.ELVProbeLeftCapField
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumCoordinates
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeLeftCapFieldConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev γ (i : Bool) : List Bool := [!i]
private def M1 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N1 (i : Bool) := probeOldModule D m Sc (γ i) M1
private abbrev hN1 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc (γ i) M1
private def O1 (i : Bool) := probeOrdinaryModuleSuperfunctor D Sc m (γ i) (N1 i) (hN1 i)
private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0

private theorem absent (i : Bool) : i ∉ γ i := by cases i <;> decide
private theorem absent0 (i : Bool) : i ∉ ([] : List Bool) := by simp
private abbrev Q (μ : List Bool) := probeOldOrdinaryFunctor D Sc m μ
private def O0 := probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0
private abbrev w (i : Bool) : OldContentCategory D Sc cut (γ i) :=
  oldContentObject D Sc cut (γ i) ⟨γ i,List.Perm.refl _⟩
private abbrev vacuum : OldContentCategory D Sc cut [] :=
  oldContentObject D Sc cut [] ⟨[],List.Perm.refl _⟩
private abbrev count (i : Bool) (μ : List Bool) := CyclotomicCrossingTensor.contentUnitCount D cut i (μ : Multiset Bool)
private theorem count_pos (i : Bool) : 0 < count i (γ i) := by cases i <;> decide
private theorem count0_pos (i : Bool) : 0 < count i [] := by cases i <;> decide
private def last (i : Bool) : Fin (count i (γ i)) := ⟨count i (γ i) - 1, Nat.sub_lt (count_pos i) (by decide)⟩
private def last0 (i : Bool) : Fin (count i []) := ⟨count i [] - 1, Nat.sub_lt (count0_pos i) (by decide)⟩

/-- The ACTUAL native coefficient cap is preserved for every row and both
moving parities, with no compatibility premise left unproved. -/
example (i : Bool) (r : Fin (count i (γ i))) :=
  probeMissingColourUnitCoefficient_cap D Sc m (γ i) (N1 i) (hN1 i) i (absent i) (w i) r
example (i : Bool) (r : Fin (count i (γ i))) :=
  probeMissingColourUnitCoefficient_surjective D Sc m (γ i) (N1 i) (hN1 i) i (absent i) (w i) r
example (i : Bool) :=
  probeMissingColourUnitCoefficient_cap D Sc m (γ i) (N1 i) (hN1 i) i (absent i) (w i) (last i)
/-- Genuine EMPTY output, including the actual existing top row. -/
example (i : Bool) (r : Fin (count i [])) :=
  probeMissingColourUnitCoefficient_cap D Sc m [] N0 hN0 i (absent0 i) vacuum r
example (i : Bool) :=
  probeMissingColourUnitCoefficient_cap D Sc m [] N0 hN0 i (absent0 i) vacuum (last0 i)
example (i : Bool) :=
  probeMissingColourUnitCoefficient_surjective D Sc m [] N0 hN0 i (absent0 i) vacuum (last0 i)
/-- Its ordinary inverse top coefficient is NONZERO on the actual regular
probe: the canonical nonzero ground value has a preimage. -/
example (i : Bool) : probeMissingColourUnitCoefficient D Sc m [] N0 hN0 i (absent0 i) vacuum (last0 i) ≠ 0 := by
  let ev := (probeVacuumScalarEquiv D Sc m).trans
    (probeOutputValueLinearEquiv D Sc m [] N0 hN0 vacuum)
  have hv : ev 1 ≠ 0 := by
    intro hzero
    have hsame : ev 1 = ev 0 := hzero.trans ev.map_zero.symm
    exact one_ne_zero (ev.injective hsame)
  obtain ⟨x, hx⟩ := probeMissingColourUnitCoefficient_surjective D Sc m [] N0 hN0 i
    (absent0 i) vacuum (last0 i) (ev 1)
  intro hz
  have hxzero := congrArg (fun f => f x) hz
  exact hv (hx.symm.trans hxzero)

end ProbeLeftCapFieldConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeLeftCapField
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
