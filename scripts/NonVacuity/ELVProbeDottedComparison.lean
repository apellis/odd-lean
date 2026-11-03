import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDottedComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeDottedComparisonConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev ν : List Bool := [false,true]
private def M := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 2)
private def N := probeOldModule D m Sc ν M
private abbrev hN := probeOldModule_evaluatesCoefficients D m Sc ν M
private def O := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
private abbrev J (μ : List Bool) (i : Bool) := ELVOld.oldContentAppend D Sc cut μ i
private abbrev T (μ : List Bool) (i : Bool) := probeOrdinaryAppend D Sc m μ i
private abbrev Q (μ : List Bool) := probeOldOrdinaryFunctor D Sc m μ
private abbrev h (μ : List Bool) (i : Bool) := probeOldOrdinaryFunctor_append D Sc m μ i

private def M1 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 3)
private def N1 (i : Bool) := probeOldModule D m Sc (i :: ν) M1
private abbrev hN1 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc (i :: ν) M1
private def O1 (i : Bool) := probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) (N1 i) (hN1 i)

private theorem eqIso_mem
    {k C : Type} [CommRing k] [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (h : F = G) :
    (eqToIso h).hom ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem F

private abbrev R (i : Bool) := (restriction (J ν i)).obj (N1 i)
private abbrev hR (i : Bool) := probeOldRestriction_evaluatesCoefficients D Sc m ν i (N1 i) (hN1 i)
private abbrev P (i : Bool) := (restriction (T ν i)).obj (O1 i)
private abbrev c (i : Bool) := eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i (N1 i) (hN1 i))
private abbrev hc (i : Bool) := eqIso_mem (probeOrdinaryRestrictionModule_eq D Sc m ν i (N1 i) (hN1 i))

/-- The canonical lower source comparison for the prescribed cap retains the
same signed moving dot, for both colours on connected mixed modules. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMappedAppendLinear_dot D Sc m ν (R i) (hR i) (P i) (c i) i (hc i) w

/-- Every power uses the original signed dot; no replacement generator is chosen. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :=
  probeMappedAppendLinear_dot_pow D Sc m ν (R i) (hR i) (P i) (c i) i (hc i) w n

private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0
private def O0 := probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0
private abbrev s0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩

private def M01 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N01 (i : Bool) := probeOldModule D m Sc [i] M01

private abbrev hN01 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc [i] M01
private def O01 (i : Bool) := probeOrdinaryModuleSuperfunctor D Sc m [i] (N01 i) (hN01 i)

/-- Vacuum includes every power of the odd moving dot and the actual source restriction equality. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut [i]) (n : ℕ) :=
  probeMappedAppendLinear_dot_pow D Sc m []
    ((restriction (J [] i)).obj (N01 i))
    (probeOldRestriction_evaluatesCoefficients D Sc m [] i (N01 i) (hN01 i))
    ((restriction (T [] i)).obj (O01 i))
    (eqToIso (probeOrdinaryRestrictionModule_eq D Sc m [] i (N01 i) (hN01 i))) i
    (eqIso_mem (probeOrdinaryRestrictionModule_eq D Sc m [] i (N01 i) (hN01 i))) w n

end ProbeDottedComparisonConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeDottedComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
