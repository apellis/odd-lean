import OddMath.SKM.PairingExtensionBubbles
import OddMath.QuiverHecke.PairingExtensionAffine
import OddMath.SKM.BubbleCoefficientBasis
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
namespace NonVacuity.PairingExtensionComparisons
/-- Two connected odd colours with an independent original coroot-kernel coordinate. -/
private def D : SKM.Datum Bool ((Bool → ℤ) × ℤ) where
  cd :=
    { root := fun j => (fun i => if i = j then 2 else -2, 0)
      coroot := fun i => (LinearMap.proj i).comp (LinearMap.fst ℤ (Bool → ℤ) ℤ)
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split_ifs <;> norm_num

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit

private def μ : (Bool → ℤ) × ℤ := (fun i => if i then -5 else 3, 7)
private def s : List Bool := [false, true, false]



private abbrev De := ReservoirWeights.pairingExtension D
private abbrev Se := ReservoirWeights.pairingExtensionScalars D Sc
private def cs : SKM.CScalars Sc where
  c ν _ := if ν.2 = 0 then 1 else -1
  shift ν i j := by
    change (if ν.2 + 0 = 0 then (1 : ℚˣ) else -1) = 1 * (if ν.2 = 0 then 1 else -1)
    simp
private abbrev ce := ReservoirWeights.pairingExtensionCScalars D cs
private def a : SKM.SYM D ℚ :=
  SKM.SYM.coefficientBasis D ℚ (0, {⟨false,rfl⟩, ⟨true,rfl⟩})
private theorem a_ne_zero : a ≠ 0 := (SKM.SYM.coefficientBasis D ℚ).ne_zero _

/-- The original kernel coordinate controls the supplied units and is not discarded. -/
example : cs.c μ false = -1 ∧ ce.c (μ,0) false = -1 := by norm_num [cs, μ]
example : SKM.PairingExtension.coefficientEquiv D a ≠ 0 := by
  intro h
  apply a_ne_zero
  apply (SKM.PairingExtension.coefficientEquiv (k := ℚ) D).injective
  exact h.trans (map_zero _).symm

/-- Full nonzero two-odd exterior coefficients retain their normalized source placement. -/
example : SKM.PairingExtension.homMap D Sc μ (upWord s) (upWord s)
    (SKM.bubAt D Sc μ (upWord s) (SKM.betaSYM cs μ a)) =
      SKM.bubAt De Se (μ,0) (upWord s)
        (SKM.betaSYM ce (μ,0) (SKM.PairingExtension.coefficientEquiv D a)) :=
  SKM.PairingExtension.homMap_bubAt_betaSYM D Sc cs μ (upWord s) a

example : SKM.PairingExtension.homMap D Sc μ [] [SKM.up false,SKM.dn false]
    (SKM.etaP cs false μ) = SKM.etaP ce false (μ,0) :=
  SKM.PairingExtension.homMap_etaP D Sc cs false μ
example : SKM.PairingExtension.homMap D Sc μ [SKM.dn true,SKM.up true] []
    (SKM.epsP cs true μ) = SKM.epsP ce true (μ,0) :=
  SKM.PairingExtension.homMap_epsP D Sc cs true μ

private def cross : ob D [false,true] ⟶ ob D [true,false] :=
  mkD D [([], Shape.cross false true, [])] (by exact ⟨rfl,rfl⟩)

/-- The exact source affine crossing is retained through upward weight labelling. -/
example : SKM.PairingExtension.homMap D Sc μ (upWord [false,true]) (upWord [true,false])
    ((alpha D Sc μ).map ((pres D Sc).diag cross)) =
      (alpha De Se (μ,0)).map
        ((QuiverHecke.PairingExtension.presentationFunctor D Sc).map ((pres D Sc).diag cross)) :=
  QuiverHecke.PairingExtension.alpha_map D Sc μ ((pres D Sc).diag cross)

example : (QuiverHecke.PairingExtension.presentationFunctor D Sc).map ((pres D Sc).diag cross) =
    (pres De Se).diag cross := QuiverHecke.PairingExtension.presentationFunctor_diag D Sc cross

end NonVacuity.PairingExtensionComparisons

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.SKM.PairingExtensionBubbles, `OddMath.QuiverHecke.PairingExtensionAffine] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}: standard axioms only"
