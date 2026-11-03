import OddMath.QuiverHecke.CyclotomicAction.ELVOperatorPowerComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace OperatorPowerComparisonConsumer
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

private theorem even_total
    {k C : Type} [CommRing k] [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (f : F ⟶ G)
    (hf : f ∈ parity (R := k) _ _ 0) (w : C) :
    f.total w ∈ SVec.parityHom (F.obj w) (G.obj w) 0 := by
  change f.app 0 w + f.app 1 w ∈ _
  rw [Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide) w, add_zero]
  exact f.app_mem 0 w

private abbrev U (i : Bool) := Q (i :: ν)
private abbrev V (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) : SVec ℚ :=
  (induced (J ν i) N).obj w
private abbrev W (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) : SVec ℚ :=
  (induced (T ν i) O).obj ((U i).obj w)
private abbrev C (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeAppendComparisonLinear D Sc m ν N hN i w
private abbrev f (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeOldContentInductionDot D Sc m ν i N w
private abbrev g (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) O ((U i).obj w)
private abbrev hc (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  even_total (probeAppendOrdinaryModuleIso D Sc m ν N hN i).hom
    (probeAppendOrdinaryModuleIso_hom_mem D Sc m ν N hN i) ((U i).obj w)

/-- Arbitrary powers of both actual moving dots under the selected comparison. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :=
  intertwine_pow (C i w) (f i w) (g i w)
    (probeAppendOrdinaryModuleIso_hom_dot D Sc m ν N hN i w) n

/-- The pointwise power form includes every old coend vector. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) (x : V i w) :=
  intertwine_pow_apply (LinearMap.id : V i w →ₗ[ℚ] V i w) (f i w) (f i w)
    (fun _ => rfl) n x

/-- The same nontrivial even comparison preserves all output parity involutions. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  intertwine_sgn (V i w) (W i w) (C i w) (hc i w) q

/-- Cap sign and full output parity survive the actual dot power comparison. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) (x : V i w) :=
  intertwine_capRowSign_apply (V i w) (W i w) (C i w) (hc i w) (f i w) (g i w)
    (probeAppendOrdinaryModuleIso_hom_dot D Sc m ν N hN i w) n x

private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0
private def O0 := probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0
private abbrev s0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩

/-- Vacuum includes both dot parities and every nonnegative power. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut [i]) (n : ℕ) :=
  intertwine_pow (probeAppendComparisonLinear D Sc m [] N0 hN0 i w)
    (probeOldContentInductionDot D Sc m [] i N0 w)
    (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m [] i) O0 ((Q [i]).obj w))
    (probeAppendOrdinaryModuleIso_hom_dot D Sc m [] N0 hN0 i w) n

end OperatorPowerComparisonConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOperatorPowerComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
