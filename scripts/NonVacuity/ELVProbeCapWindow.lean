import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapWindow
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace NonVacuity.ELVProbeCapWindow
private theorem nonzero_of_extracts {V : Type} [AddCommGroup V] [Module ℚ V]
    (f : V →ₗ[ℚ] ℚ) (v : V) (h : f v = 1) : v ≠ 0 := by
  intro hz
  have hv : f v = 0 := (congrArg f hz).trans f.map_zero
  exact zero_ne_one (hv.symm.trans h)

private theorem signed_square_apply (V : SVec ℚ) (x : End V)
    (h : (x ^ 2 + 1) ^ 1 = 0) (v : V) :
    SVec.toLinearMap (x ^ 2) v = -v := by
  have he : x ^ 2 + 1 = 0 := by simpa only [pow_one] using h
  have hv := congrArg (fun f : End V => SVec.toLinearMap f v) he
  change SVec.toLinearMap (x ^ 2) v + v = 0 at hv
  exact eq_neg_of_add_eq_zero_left hv

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private theorem odd (i : Bool) : D.parity i = 1 := by cases i <;> rfl
private abbrev V (i : Bool) := (ProbeVacuumCap.source D Sc m i).obj (probeOldVacuumObject D Sc m)
private def topVector (i : Bool) : V i :=
  SVec.toLinearMap (ProbeVacuumCap.dot D Sc m i ^ (probeCutoff D m i - 1))
    (ProbeVacuumCap.unitVector D Sc m i (1 : ℚ))

/-- On both positive odd-colour cutoffs 2 and 4, the actual native last
coefficient cap extracts one from its prescribed top unit/dot vector. -/
private theorem extracts_top (i : Bool) :
    ProbeVacuumCap.groundRow D Sc m i (positive i) (topVector i) = 1 := by
  have h := ProbeVacuumCap.groundRow_dot_unit D Sc m i (positive i)
    (probeCutoff D m i - 1) (Nat.sub_lt (positive i) (by decide)) (1 : ℚ)
  rw [ite_eq_left (Nat.sub_add_cancel (positive i))] at h
  convert h using 1
  congr 1

private theorem top_ne_zero (i : Bool) : topVector i ≠ 0 :=
  nonzero_of_extracts (ProbeVacuumCap.groundRow D Sc m i (positive i))
    (topVector i) (extracts_top i)

example (i : Bool) : topVector i ≠ 0 := top_ne_zero i

/-- Every scalar is recovered on the actual specified native unit/dot
vectors, rather than solely on arbitrary surjectivity witnesses. -/
example (i : Bool) (c : ℚ) :
    ProbeVacuumCap.groundRow D Sc m i (positive i)
      (SVec.toLinearMap (ProbeVacuumCap.dot D Sc m i ^ (probeCutoff D m i - 1))
        (ProbeVacuumCap.unitVector D Sc m i c)) = c := by
  have h := ProbeVacuumCap.groundRow_dot_unit D Sc m i (positive i)
    (probeCutoff D m i - 1) (Nat.sub_lt (positive i) (by decide)) c
  rw [ite_eq_left (Nat.sub_add_cancel (positive i))] at h
  exact h

example (i : Bool) : (ProbeVacuumCap.dot D Sc m i ^ 2 + 1) ^ m i = 0 :=
  ProbeVacuumCap.dot_odd_polynomial D Sc m i (odd i)
/-- On that same occupied native vector, the smallest odd-colour probe has
D² = -1, rather than +1. -/
example : SVec.toLinearMap (ProbeVacuumCap.dot D Sc m false ^ 2) (topVector false) =
    -(topVector false) :=
  signed_square_apply (V false) (ProbeVacuumCap.dot D Sc m false)
    (ProbeVacuumCap.dot_odd_polynomial D Sc m false (odd false)) (topVector false)
end NonVacuity.ELVProbeCapWindow
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapWindow] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "No owned declarations: {owner}"
    for name in names do
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
