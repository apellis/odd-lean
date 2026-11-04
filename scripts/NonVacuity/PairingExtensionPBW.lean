import OddMath.QuiverHecke.PairingExtensionPBW
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
namespace NonVacuity.PairingExtensionPBW
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


private abbrev De := ReservoirWeights.pairingExtension D
private abbrev Se := ReservoirWeights.pairingExtensionScalars D Sc
private def ni : NFIdx [false,true] [false,true] := by
  have hc : Categorification.TypeA.canWord 2 1 = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([0,1],1), by decide, by decide, ?_⟩
  change SChain [false,true]
    (pl [false,true] ([0,1].map PG.dot ++ cw (Categorification.TypeA.canWord 2 1))) [false,true]
  rw [hc]
  simp only [cw, List.reverse_nil, List.map_nil, List.append_nil]
  simpa only [tgt_map_dot] using sChain_pl [false,true] ([0,1].map PG.dot)
private def idx : SKM.SYM.CoefficientIndex D × NFIdx [false,true] [false,true] :=
  ((Finsupp.single (false,0) 1, {⟨false,rfl⟩, ⟨true,rfl⟩}), ni)
private def f := extensionBasis D Sc [false,true] [false,true] idx
private theorem degree_idx : extensionDegree D idx = 6 := by
  norm_num [extensionDegree, SKM.SYM.coefficientWeight, SKM.SYM.elementaryWeight, idx, ni, D]
private theorem low : f ∈ ExtendedAtMost D Sc [false,true] [false,true] 6 :=
  Submodule.subset_span ⟨idx, by change extensionDegree D idx ≤ 6; rw [degree_idx], rfl⟩
private theorem high : f ∈ ExtendedAtLeast D Sc [false,true] [false,true] 6 :=
  Submodule.subset_span ⟨idx, by change (6:ℤ) ≤ (extensionDegree D idx:ℤ); norm_num [degree_idx], rfl⟩

example : f ≠ 0 := (extensionBasis D Sc [false,true] [false,true]).ne_zero _
example : QuiverHecke.PairingExtension.coefficientHomEquiv D Sc _ _ f =
    extensionBasis De Se [false,true] [false,true] idx :=
  QuiverHecke.PairingExtension.coefficientHomEquiv_basis D Sc idx
example : QuiverHecke.PairingExtension.coefficientHomEquiv D Sc _ _ f ≠ 0 := by
  change QuiverHecke.PairingExtension.coefficientHomEquiv D Sc _ _
    (extensionBasis D Sc [false,true] [false,true] idx) ≠ 0
  rw [QuiverHecke.PairingExtension.coefficientHomEquiv_basis]
  exact (extensionBasis De Se [false,true] [false,true]).ne_zero _
example : QuiverHecke.PairingExtension.coefficientHomEquiv D Sc _ _ f ∈
    ExtendedAtMost De Se [false,true] [false,true] 6 :=
  QuiverHecke.PairingExtension.coefficientHomEquiv_mem_atMost D Sc low
example : QuiverHecke.PairingExtension.coefficientHomEquiv D Sc _ _ f ∈
    ExtendedAtLeast De Se [false,true] [false,true] 6 :=
  QuiverHecke.PairingExtension.coefficientHomEquiv_mem_atLeast D Sc high
example : (QuiverHecke.PairingExtension.affineEquiv D Sc [false,true] [false,true]).symm
    ((QuiverHecke.PairingExtension.presentationFunctor D Sc).map (ni.nf (D:=D) (Sc:=Sc))) =
    ni.nf (D:=D) (Sc:=Sc) := by
  rw [← QuiverHecke.PairingExtension.affineEquiv_apply, LinearEquiv.symm_apply_apply]

end NonVacuity.PairingExtensionPBW

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.PairingExtensionPBW
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"
