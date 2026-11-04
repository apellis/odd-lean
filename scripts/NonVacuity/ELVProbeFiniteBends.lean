import OddMath.QuiverHecke.CyclotomicAction.ELVProbeFiniteBends
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
namespace ProbeFiniteBendsConsumer
local instance homPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private def ΛP : Bool → ℤ := fun i => probeCutoff D m i
private def cutoff : Bool → ℕ := fun _ => 4
private def ΛR : Bool → ℤ := fun _ => 4
private theorem hP (i : Bool) : (probeCutoff D m i : ℤ) = D.h i ΛP := rfl
private theorem hR (i : Bool) : (cutoff i : ℤ) = D.h i ΛR := rfl
private abbrev P := elvProbeReservoir D Sc m cutoff 12 ΛP ΛR hP hR
private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

-- Every input Hom object and every supported probe/content input are retained.
example (t : Sector Bool) (Z : P.H t) (M : P.T.obj (-P.muP t))
    (δ : WeightBlocks D ΛR (P.muM t)) :=
  elvProbeDx_even_expansion D Sc m cutoff 12 ΛP ΛR hP hR false t Z M δ sy hc rfl
example (t : Sector Bool) (Z : P.H t) (M : P.T.obj (-P.muP t))
    (δ : WeightBlocks D ΛR (P.muM t)) :=
  elvProbeDx_odd_expansion D Sc m cutoff 12 ΛP ΛR hP hR true t Z M δ sy hc rfl
example (t : Sector Bool) (hb : StepValid (false, false) true t)
    (hv : StepValid (true, false) false t) (Z : P.H t)
    (M : P.T.obj (-P.muP t)) (δ : WeightBlocks D ΛR (P.muM t)) :=
  elvProbeCx_even_expansion D Sc m cutoff 12 ΛP ΛR hP hR false t hb hv Z M δ sy hc rfl
example (t : Sector Bool) (hb : StepValid (false, true) true t)
    (hv : StepValid (true, true) false t) (Z : P.H t)
    (M : P.T.obj (-P.muP t)) (δ : WeightBlocks D ΛR (P.muM t)) :=
  elvProbeCx_odd_expansion D Sc m cutoff 12 ΛP ΛR hP hR true t hb hv Z M δ sy hc rfl

private def corner (i : Bool) : Sector Bool := (Finsupp.single i 1, Finsupp.single i 1)

-- Both pure corners occur at this specified nonempty sector. Their
-- validity conditions are proved, while coefficient inputs remain arbitrary.
example (Z : P.H (corner true)) (M : P.T.obj (-P.muP (corner true)))
    (δ : WeightBlocks D ΛR (P.muM (corner true))) :=
  elvProbeCx_odd_expansion D Sc m cutoff 12 ΛP ΛR hP hR true (corner true)
    (by simp [corner, StepValid]) (by simp [corner, StepValid]) Z M δ sy hc rfl
example (Z : P.H (corner false)) (M : P.T.obj (-P.muP (corner false)))
    (δ : WeightBlocks D ΛR (P.muM (corner false))) :=
  elvProbeCx_even_expansion D Sc m cutoff 12 ΛP ΛR hP hR false (corner false)
    (by simp [corner, StepValid]) (by simp [corner, StepValid]) Z M δ sy hc rfl

-- The scalar probe used by this pair has a nonzero vacuum input at both parities.
example (i : Bool) : probeOldVacuumAppendVector D (parameterTwist D Sc) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D (parameterTwist D Sc) m i (by cases i <;> decide)

end ProbeFiniteBendsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVProbeBendEvaluation,
      `OddMath.QuiverHecke.SwappedAssembly.Sigma.FiniteBendEvaluation,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeFiniteBends] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
