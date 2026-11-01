import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixBijective
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace KernelMatrixBijectiveConsumer
open CyclotomicAction.AsymmetricParameters
private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num




private abbrev oddColour : {i : Bool // mixedDatum.parity i = 1} := ⟨true, rfl⟩
private abbrev evenColour : {i : Bool // mixedDatum.parity i = 0} := ⟨false, rfl⟩
def src (n : ℕ) (ν : List Bool) : OldContentCategory mixedDatum mixedScalars (fun _ => n) ν :=
  ⟨⟨ν.reverse⟩, List.reverse_perm ν⟩


theorem oddPositiveHeight : 0 ≤ contentCrossingHeight mixedDatum (fun _ => 4) true ([false,true] : Multiset Bool) := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
example : Function.Bijective ((actualPositiveKernelMap mixedDatum mixedScalars (fun _ => 4) true
    (contentUnitCount mixedDatum (fun _ => 4) true ([false,true] : Multiset Bool))
    (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))).app
      (op (⟨([false,true] : List Bool).reverse⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)))) :=
  actualPositiveKernelMap_bijective mixedDatum mixedScalars (fun _ => 4) true
    ⟨[false,true]⟩ oddPositiveHeight ⟨([false,true] : List Bool).reverse⟩
example : Function.Bijective ((actualPositiveKernelMap mixedDatum mixedScalars (fun _ => 4) true
    (contentUnitCount mixedDatum (fun _ => 4) true ([false,true] : Multiset Bool))
    (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))).app
      (op (⟨[]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)))) :=
  actualPositiveKernelMap_bijective mixedDatum mixedScalars (fun _ => 4) true
    ⟨[false,true]⟩ oddPositiveHeight ⟨[]⟩

theorem evenPositiveHeight : 0 ≤ contentCrossingHeight mixedDatum (fun _ => 4) false ([false,true] : Multiset Bool) := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
example : Function.Bijective ((actualPositiveKernelMap mixedDatum mixedScalars (fun _ => 4) false
    (contentUnitCount mixedDatum (fun _ => 4) false ([false,true] : Multiset Bool))
    (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))).app
      (op (⟨([false,true] : List Bool).reverse⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)))) :=
  actualPositiveKernelMap_bijective mixedDatum mixedScalars (fun _ => 4) false
    ⟨[false,true]⟩ evenPositiveHeight ⟨([false,true] : List Bool).reverse⟩
example : Function.Bijective ((actualPositiveKernelMap mixedDatum mixedScalars (fun _ => 4) false
    (contentUnitCount mixedDatum (fun _ => 4) false ([false,true] : Multiset Bool))
    (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))).app
      (op (⟨[]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)))) :=
  actualPositiveKernelMap_bijective mixedDatum mixedScalars (fun _ => 4) false
    ⟨[false,true]⟩ evenPositiveHeight ⟨[]⟩

theorem oddNegativeHeight : contentCrossingHeight mixedDatum (fun _ => 1) true ([false,true,true,true,true] : Multiset Bool) ≤ 0 := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
example : Function.Bijective ((actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 1) true
    (contentCapCount mixedDatum (fun _ => 1) true ([false,true,true,true,true] : Multiset Bool))
    (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))).app
      (op (⟨([false,true,true,true,true] : List Bool).reverse⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)))) :=
  actualNegativeKernelMap_bijective mixedDatum mixedScalars (fun _ => 1) true
    ⟨[false,true,true,true,true]⟩ oddNegativeHeight ⟨([false,true,true,true,true] : List Bool).reverse⟩
example : Function.Bijective ((actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 1) true
    (contentCapCount mixedDatum (fun _ => 1) true ([false,true,true,true,true] : Multiset Bool))
    (⟨[false,true,true,true,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))).app
      (op (⟨[]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)))) :=
  actualNegativeKernelMap_bijective mixedDatum mixedScalars (fun _ => 1) true
    ⟨[false,true,true,true,true]⟩ oddNegativeHeight ⟨[]⟩

theorem evenNegativeHeight : contentCrossingHeight mixedDatum (fun _ => 1) false ([false,false,false,true] : Multiset Bool) ≤ 0 := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
example : Function.Bijective ((actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 1) false
    (contentCapCount mixedDatum (fun _ => 1) false ([false,false,false,true] : Multiset Bool))
    (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))).app
      (op (⟨([false,false,false,true] : List Bool).reverse⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)))) :=
  actualNegativeKernelMap_bijective mixedDatum mixedScalars (fun _ => 1) false
    ⟨[false,false,false,true]⟩ evenNegativeHeight ⟨([false,false,false,true] : List Bool).reverse⟩
example : Function.Bijective ((actualNegativeKernelMap mixedDatum mixedScalars (fun _ => 1) false
    (contentCapCount mixedDatum (fun _ => 1) false ([false,false,false,true] : Multiset Bool))
    (⟨[false,false,false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))).app
      (op (⟨[]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)))) :=
  actualNegativeKernelMap_bijective mixedDatum mixedScalars (fun _ => 1) false
    ⟨[false,false,false,true]⟩ evenNegativeHeight ⟨[]⟩

end KernelMatrixBijectiveConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixCoordinates,
      `OddMath.QuiverHecke.CyclotomicAction.ELVKernelOffContentMatrices,
      `OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixBijective] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} owned declarations in {owner}"
