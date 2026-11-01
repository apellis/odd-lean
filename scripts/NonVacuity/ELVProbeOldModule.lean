import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldModule
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open scoped Classical
namespace ELVProbeOldModuleConsumer
open Examples
private def m : Unit → ℕ := fun _ => 3
private abbrev cut := probeCutoff datum m
private abbrev a : Unit → Polynomial ℚ := probePolynomial (probeDotExponent datum) m
private abbrev G := heightParity datum scalars a (probePolynomial_parity datum m) 0
private abbrev M := SuperBimodule.regular G
private abbrev v : ELVOld.OldContentCategory datum scalars cut [] :=
  ELVOld.oldContentObject datum scalars cut [] ⟨[],List.Perm.refl []⟩

private theorem e_one : probeOldWordIdempotent datum m scalars [] v = (1 : Hn datum scalars 0) := by
  have h : (Finset.univ : Finset (Word Unit 0)) = {vacuumWord} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    exact List.length_eq_zero_iff.mp w.property
  change FiniteHomMatrix.single vacuumWord vacuumWord (𝟙 _) = FiniteHomMatrix.localUnit Finset.univ
  rw [h]
  simp [FiniteHomMatrix.localUnit, FiniteHomMatrix.idem]

private def point : (probeOldModule datum m scalars [] M).obj v :=
  ⟨(1 : Hn datum scalars 0), by change probeOldWordIdempotent datum m scalars [] v * 1 = 1; rw [e_one,one_mul]⟩

/-- The closed fixture is an actual nonzero module vector. -/
example : point ≠ 0 := by
  intro h
  have he := congrArg (fun x : (probeOldModule datum m scalars [] M).obj v =>
    (show Hn datum scalars 0 from (show probeOldWordSubmodule datum m scalars [] M v from x).val)) h
  change (1 : Hn datum scalars 0) = 0 at he
  apply VacuumExamples.vacuum_unit_ne_zero
  rw [he, map_zero]

example : (probeOldModule datum m scalars [] M).map (𝟙 v) point = point := by
  change (probeOldModuleFunctor datum m scalars [] M).map (𝟙 v) point = point
  rw [CategoryTheory.Functor.map_id]
  rfl

example : (probeOldModule datum m scalars [] M).map ((2 : ℚ) • 𝟙 v) point = (2 : ℚ) • point := by
  change (probeOldModuleFunctor datum m scalars [] M).map ((2 : ℚ) • 𝟙 v) point = (2 : ℚ) • point
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

example : (probeOldModule datum m scalars [] M).map (𝟙 v) ∈
    Supercategory.parity (R := ℚ) _ _ 0 :=
  (probeOldModule datum m scalars [] M).map_mem (Supercategory.id_mem v)

end ELVProbeOldModuleConsumer

namespace ELVProbeOldMixedConsumer
private def D : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun i j => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by
        simp [CartanDatum.cartanMatrix_apply, Ne.symm h]
      zero_comm := fun i j => by
        by_cases h : i = j
        · subst j
          simp [CartanDatum.cartanMatrix_apply]
        · simp [CartanDatum.cartanMatrix_apply, h, Ne.symm h] }
  parity := fun i => if i then 0 else 1
  even_of_odd := by
    intro i j _
    change Even (if j = i then (2 : ℤ) else 0)
    split_ifs <;> norm_num

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit


private def m : Bool → ℕ := fun i => if i then 5 else 3
private abbrev cut := probeCutoff D m
private abbrev ν : List Bool := [false,true]
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev G := heightParity D Sc a (probePolynomial_parity D m) 2
private abbrev M := SuperBimodule.regular G
private abbrev v : ELVOld.OldContentCategory D Sc cut ν :=
  ELVOld.oldContentObject D Sc cut ν ⟨ν,List.Perm.refl ν⟩
private def point : (probeOldModule D m Sc ν M).obj v :=
  ⟨(probeOldWordIdempotent D m Sc ν v : heightAlgebra D Sc a 2), by
    change probeOldWordIdempotent D m Sc ν v * probeOldWordIdempotent D m Sc ν v =
      probeOldWordIdempotent D m Sc ν v
    unfold probeOldWordIdempotent
    rw [← map_mul, Hn.wordIdempotent_sq]⟩

example : (probeOldModule D m Sc ν M).map (𝟙 v) point = point := by
  change (probeOldModuleFunctor D m Sc ν M).map (𝟙 v) point = point
  rw [CategoryTheory.Functor.map_id]
  rfl

example : (probeOldModule D m Sc ν M).map ((2 : ℚ) • 𝟙 v) point = (2 : ℚ) • point := by
  change (probeOldModuleFunctor D m Sc ν M).map ((2 : ℚ) • 𝟙 v) point = (2 : ℚ) • point
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl
end ELVProbeOldMixedConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldModule
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."

