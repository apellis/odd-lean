import OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ContentGridInverseConsumer
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



abbrev C := OldCategory mixedDatum mixedScalars (fun _ => 4)

private abbrev v : C := ⟨[false, true]⟩
private abbrev source : OldContentCategory mixedDatum mixedScalars (fun _ => 4) [false, true] :=
  ⟨v, List.Perm.refl _⟩
private def block : Superfunctor ℚ
    (OldContentCategory mixedDatum mixedScalars (fun _ => 4) [false, true]) (SVec ℚ) :=
  (BalancedInduction.restriction
    (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) [false, true])).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4) v)
private def upperBlock (i : Bool) : Superfunctor ℚ
    (OldContentCategory mixedDatum mixedScalars (fun _ => 4) (i :: [false, true])) (SVec ℚ) :=
  (BalancedInduction.restriction
    (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) (i :: [false, true]))).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4)
      ((append mixedDatum mixedScalars (fun _ => 4) i).obj v))

private def pureSource (r : ℕ) (i : Bool) :
    OldContentCategory mixedDatum mixedScalars (fun _ => 4) (List.replicate r i) :=
  ⟨⟨List.replicate r i⟩, List.Perm.refl _⟩
private def pureUpper (r : ℕ) (i : Bool) : Superfunctor ℚ
    (OldContentCategory mixedDatum mixedScalars (fun _ => 4) (i :: List.replicate r i)) (SVec ℚ) :=
  (BalancedInduction.restriction
    (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) (i :: List.replicate r i))).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4)
      ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource r i).obj))
private def pureVector (r : ℕ) (i : Bool) :
    (pureUpper r i).obj ((oldContentAppend mixedDatum mixedScalars (fun _ => 4)
      (List.replicate r i) i).obj (pureSource r i)) := by
  change (append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource r i).obj ⟶
    (append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource r i).obj
  exact 𝟙 _

private theorem unitSign (i : Bool) :
    0 ≤ contentCrossingHeight mixedDatum (fun _ => 4) i ([i] : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
private theorem capSign (i : Bool) :
    contentCrossingHeight mixedDatum (fun _ => 4) i ([i,i,i] : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
private theorem zeroUnitSign (i : Bool) :
    0 ≤ contentCrossingHeight mixedDatum (fun _ => 4) i ([i,i] : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
private theorem zeroCapSign (i : Bool) :
    contentCrossingHeight mixedDatum (fun _ => 4) i ([i,i] : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
private theorem zeroUnitCount (i : Bool) :
    contentUnitCount mixedDatum (fun _ => 4) i ([i,i] : Multiset Bool) = 0 := by
  cases i <;> norm_num [contentUnitCount,contentCrossingHeight,mixedDatum,datum,SKM.Datum.h,SKM.Datum.α]
private theorem zeroCapCount (i : Bool) :
    contentCapCount mixedDatum (fun _ => 4) i ([i,i] : Multiset Bool) = 0 := by
  cases i <;> norm_num [contentCapCount,contentCrossingHeight,mixedDatum,datum,SKM.Datum.h,SKM.Datum.α]

/-- The generic assembled module maps retain even degree after substitution. -/
example (i : Bool) (m : ℕ) := BalancedInduction.gridUnitMatrixModuleMap_mem
  (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [] i)
  (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [i] i)
  (oldContentMatrixCross_supernatural mixedDatum mixedScalars (fun _ => 4) [] i)
  (oldContentAppendDot_supernatural mixedDatum mixedScalars (fun _ => 4) [i] i)
  (pureUpper 0 i) m
example (i : Bool) (m : ℕ) := BalancedInduction.gridCapMatrixModuleMap_mem
  (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [i,i] i)
  (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [i,i,i] i)
  (oldContentMatrixCross_supernatural mixedDatum mixedScalars (fun _ => 4) [i,i] i)
  (oldContentAppendDot_supernatural mixedDatum mixedScalars (fun _ => 4) [i,i] i)
  (pureUpper 2 i) m

/-- Both moving parities, positive-height prescribed unit count. -/
example (i : Bool) := oldContentGridUnitMatrixIso mixedDatum mixedScalars (fun _ => 4) [] i
  (pureUpper 0 i) (unitSign i)
example (i : Bool) := oldContentGridUnitMatrixIso_hom mixedDatum mixedScalars (fun _ => 4) [] i
  (pureUpper 0 i) (unitSign i)
example (i : Bool) := oldContentGridUnitMatrixIso_inv_mem mixedDatum mixedScalars (fun _ => 4) [] i
  (pureUpper 0 i) (unitSign i)

/-- Both moving parities, negative-height prescribed cap count. -/
example (i : Bool) := oldContentGridCapMatrixIso mixedDatum mixedScalars (fun _ => 4) [i,i] i
  (pureUpper 2 i) (capSign i)
example (i : Bool) := oldContentGridCapMatrixIso_hom mixedDatum mixedScalars (fun _ => 4) [i,i] i
  (pureUpper 2 i) (capSign i)
example (i : Bool) := oldContentGridCapMatrixIso_inv_mem mixedDatum mixedScalars (fun _ => 4) [i,i] i
  (pureUpper 2 i) (capSign i)

/-- Height zero has both given mate-only inverse presentations. -/
example (i : Bool) := oldContentGridUnitMatrixIso mixedDatum mixedScalars (fun _ => 4) [i] i
  (pureUpper 1 i) (zeroUnitSign i)
example (i : Bool) := oldContentGridCapMatrixIso mixedDatum mixedScalars (fun _ => 4) [i] i
  (pureUpper 1 i) (zeroCapSign i)

example (i : Bool)
    (t : OldContentCategory mixedDatum mixedScalars (fun _ => 4) [i]) :=
  oldContentGridUnitMatrixComponent_bijective mixedDatum mixedScalars (fun _ => 4) [] i
    (pureUpper 0 i) (unitSign i) t
example (i : Bool)
    (t : OldContentCategory mixedDatum mixedScalars (fun _ => 4) [i,i,i]) :=
  oldContentGridCapMatrixComponent_bijective mixedDatum mixedScalars (fun _ => 4) [i,i] i
    (pureUpper 2 i) (capSign i) t

end ContentGridInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
