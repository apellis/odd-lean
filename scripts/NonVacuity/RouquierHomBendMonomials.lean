import OddMath.SKM.RouquierHomBendMonomials
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierHomBendMonomials
local instance homPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private abbrev D := WeightedAppendFixture.datum
private abbrev S := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private def Λ : Bool → ℤ := fun i => probeCutoff D m i
private def cutoff : Bool → ℕ := fun _ => 4
private def ΛR : Bool → ℤ := fun _ => 4
private theorem hP (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := rfl
private theorem hR (i : Bool) : (cutoff i : ℤ) = D.h i ΛR := rfl
private abbrev P := elvProbeReservoir D S m cutoff 12 Λ ΛR hP hR
private theorem preEdge (i : Bool) : -(-Λ + D.α i) + D.α i = -(-Λ) := by abel
private theorem postEdge (i : Bool) : -ΛR + D.α i = -ΛR + D.α i := rfl
private instance dotIso (i : Bool) : IsIso (P.T.dot i (preEdge i)) :=
  (isUnit_iff_isIso _).mp
    (elvProbeReservoir_dot_isUnit D S m cutoff 12 Λ ΛR hP hR i (preEdge i))

-- Both parities, with arbitrary Hom objects and arbitrary exponents.
example (i : Bool) (β : Bool →₀ ℕ) (r : ℕ)
    (Z : homWeightSector P.T.obj P.W.obj (-Λ + D.α i) (-ΛR)) :=
  homProbeToReservoir_monomial P.T P.W i β (preEdge i) (postEdge i) r Z
example (i : Bool) (β : Bool →₀ ℕ) (r : ℕ)
    (Z : homWeightSector P.T.obj P.W.obj (-Λ) (-ΛR + D.α i)) :=
  homReservoirToProbe_monomial P.T P.W i β (preEdge i) (postEdge i) r Z
example (i : Bool) (r : ℕ)
    (Z : homWeightSector P.T.obj P.W.obj (-Λ + D.α i) (-ΛR)) :=
  homPreNegativeCap_aut P.T P.W i (preEdge i) r Z
example (i : Bool) (r : ℕ)
    (Z : homWeightSector P.T.obj P.W.obj (-Λ) (-ΛR)) :=
  homPreNegativeCup_aut P.T P.W i (preEdge i) r Z

-- The actual invertible-dot probe has occupied inputs at both colours.
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D S) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D S) m i (by cases i <;> decide)

end NonVacuity.RouquierHomBendMonomials
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierHomBendMonomials
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
