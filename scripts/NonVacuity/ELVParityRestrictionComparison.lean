import OddMath.QuiverHecke.CyclotomicAction.ELVParityRestrictionComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ParityRestrictionComparisonConsumer
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

private def e (i : Bool) : (restriction (k := ℚ) (Q (i :: ν))).obj (O1 i) ≅ N1 i :=
  eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m (i :: ν) (N1 i) (hN1 i))
private abbrev he (i : Bool) :=
  eqIso_mem (probeOrdinaryModuleSuperfunctor_restrict D Sc m (i :: ν) (N1 i) (hN1 i))

/-- The same given coordinates, for both moving colours and every target shift. -/
example (i : Bool) (q : ZMod 2) := parityRestrictionIso_eq_chain (Q (i :: ν)) (O1 i) (N1 i) (e i) q (he i)
example (i : Bool) (q : ZMod 2) := parityRestrictionIso_hom_mem (Q (i :: ν)) (O1 i) (N1 i) (e i) q (he i)
example (i : Bool) (q : ZMod 2) := parityRestrictionIso_inv_mem (Q (i :: ν)) (O1 i) (N1 i) (e i) q (he i)
example (i : Bool) (q : ZMod 2) := parityRestrictionIso_hom_coordinate (Q (i :: ν)) (O1 i) (N1 i) (e i) q (he i)
example (i : Bool) (q : ZMod 2) := parityRestrictionIso_inv_coordinate (Q (i :: ν)) (O1 i) (N1 i) (e i) q (he i)

private abbrev Mod (i : Bool) := Superfunctor ℚ (OrdinaryContentCategory D Sc a (i :: ν)) (SVec ℚ)
private abbrev Res (i : Bool) := restriction (k := ℚ) (Q (i :: ν))
private abbrev family (i : Bool) := Functor.leftUnitor (Res i)
private theorem family_mem (i : Bool) (M : Mod i) :
    (family i).hom.app M ∈ parity (R := ℚ) _ _ 0 := id_mem _

/-- The family includes ALL ordinary modules and their input maps. -/
example (i : Bool) (q : ZMod 2) (M : Mod i) :=
  parityRestrictionNatIso_app (Q (i :: ν)) (𝟭 (Mod i)) (Res i) (family i) q M
example (i : Bool) (q : ZMod 2) (M : Mod i) :=
  parityRestrictionNatIso_hom_mem (Q (i :: ν)) (𝟭 (Mod i)) (Res i) (family i) q (family_mem i) M

/-- Odd and inhomogeneous input maps are supplied by the actual appended dot. -/
example (q : ZMod 2) :=
  (parityRestrictionNatIso (Q (true :: ν)) (𝟭 (Mod true)) (Res true) (family true) q).hom.naturality
    (𝟙 (induced (T ν true) O) + transformComponent (probeOrdinaryAppendDot_supernatural D Sc m ν true) O)

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

private def e0 (i : Bool) : (restriction (k := ℚ) (Q [i])).obj (O01 i) ≅ N01 i :=
  eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m [i] (N01 i) (hN01 i))
private abbrev he0 (i : Bool) :=
  eqIso_mem (probeOrdinaryModuleSuperfunctor_restrict D Sc m [i] (N01 i) (hN01 i))

/-- The vacuum lower level uses the same canonical two-coordinate bridge. -/
example (i : Bool) (q : ZMod 2) :=
  parityRestrictionIso_inv_coordinate (Q [i]) (O01 i) (N01 i) (e0 i) q (he0 i)

end ParityRestrictionComparisonConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVParityRestrictionComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
