import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ParityMatrixCoordinatesConsumer
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


private def point (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    (O1 i).obj ((Q (i :: ν)).obj w) ≃ₗ[ℚ] (N1 i).obj w :=
  ELVOld.moduleIsoLinearEquiv (e i) w

private theorem point_total_mem
    {A : Type} [Category A] [Preadditive A] [Linear ℚ A] [Supercategory ℚ A]
    {F G : Superfunctor ℚ A (SVec ℚ)} {f : F ⟶ G}
    (hf : f ∈ parity (R := ℚ) _ _ 0) (w : A) :
    f.total w ∈ parity (R := ℚ) (F.obj w) (G.obj w) 0 := by
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) w
  rw [SuperNatTrans.total, hz, add_zero]
  exact f.app_mem 0 w

private theorem point_mem (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    SVec.ofHom (point i w).toLinearMap ∈ parity (R := ℚ) _ _ 0 := by
  exact point_total_mem (he i) w

/-- Actual old/ordinary module values, both moving colours and both shifts. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  shiftedModuleValueLinearEquiv_hom_mem (O1 i) (N1 i) ((Q (i :: ν)).obj w) w (point i w) q (point_mem i w)
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  shiftedModuleValueLinearEquiv_inv_mem (O1 i) (N1 i) ((Q (i :: ν)).obj w) w (point i w) q (point_mem i w)

private abbrev ModPi (i : Bool) : PiSupercategory ℚ
    (Superfunctor ℚ (OrdinaryContentCategory D Sc a (i :: ν)) (SVec ℚ)) :=
  ELVOld.supermodulePiSupercategory
attribute [local instance] ModPi

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2)
    (b : ((SKM.homParityShift (k := ℚ) q).obj (O1 i)).obj ((Q (i :: ν)).obj w)) :=
  shiftedModuleValueLinearEquiv_apply (O1 i) (N1 i) ((Q (i :: ν)).obj w) w (point i w) q b
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2)
    (b : ((SKM.homParityShift (k := ℚ) q).obj (O1 i)).obj ((Q (i :: ν)).obj w)) :=
  shiftedModuleValueLinearEquiv_hom_coordinate (O1 i) (N1 i) ((Q (i :: ν)).obj w) w (point i w) q b
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2)
    (b : (O1 i).obj ((Q (i :: ν)).obj w)) :=
  shiftedModuleValueLinearEquiv_inv_coordinate (O1 i) (N1 i) ((Q (i :: ν)).obj w) w (point i w) q b

/-- The Option/Fin family uses the same given slot coordinates. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (b : ℕ)
    (q : Option (Fin b) → ZMod 2) :=
  LinearEquiv.piCongrRight fun r : Option (Fin b) =>
    shiftedModuleValueLinearEquiv (O1 i) (N1 i) ((Q (i :: ν)).obj w) w (point i w) (q r)

private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0
private def O0 := probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0
private abbrev s0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩
private def e0 : (restriction (k := ℚ) (Q [])).obj O0 ≅ N0 :=
  eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m [] N0 hN0)

/-- Vacuum has the same full shifted module coordinate law. -/
example (q : ZMod 2) (b : O0.obj ((Q []).obj s0)) :=
  shiftedModuleValueLinearEquiv_inv_coordinate O0 N0 ((Q []).obj s0) s0
    (ELVOld.moduleIsoLinearEquiv e0 s0) q b

end ParityMatrixCoordinatesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixCoordinates
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
