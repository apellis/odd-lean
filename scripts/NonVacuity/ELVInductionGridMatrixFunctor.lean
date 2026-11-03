import OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixFunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace GridMatrixFunctorConsumer
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

open BalancedInduction
local notation "J" i => oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false,true] i
local notation "K" i => oldContentAppend mixedDatum mixedScalars (fun _ => 4) (i :: [false,true]) i
local notation "hX" i => oldContentMatrixCross_supernatural mixedDatum mixedScalars (fun _ => 4) [false,true] i
local notation "hD" i => oldContentAppendDot_supernatural mixedDatum mixedScalars (fun _ => 4) (i :: [false,true]) i
local notation "hL" i => oldContentAppendDot_supernatural mixedDatum mixedScalars (fun _ => 4) [false,true] i

/-- Literal full-module components and parity, for both moving parities and all sizes. -/
example (i : Bool) (m : ℕ) := gridUnitMatrixInputNatTrans_app (J i) (K i) (hX i) (hD i) m (upperBlock i)
example (i : Bool) (m : ℕ) := gridCapMatrixInputNatTrans_app (J i) (K i) (hX i) (hL i) m (upperBlock i)
example (i : Bool) (m : ℕ) := gridUnitMatrixInputNatTrans_app_mem (J i) (K i) (hX i) (hD i) m (upperBlock i)
example (i : Bool) (m : ℕ) := gridCapMatrixInputNatTrans_app_mem (J i) (K i) (hX i) (hL i) m (upperBlock i)

/-- The input maps include the chosen odd dot, and identity plus that dot. -/
example (i : Bool) (m : ℕ) :=
  (gridUnitMatrixInputNatTrans (J i) (K i) (hX i) (hD i) m).naturality
    (oldContentInductionDotComponent mixedDatum mixedScalars (fun _ => 4) [false,true] i block)
example (i : Bool) (m : ℕ) :=
  (gridCapMatrixInputNatTrans (J i) (K i) (hX i) (hL i) m).naturality
    (oldContentInductionDotComponent mixedDatum mixedScalars (fun _ => 4) [false,true] i block)
example (i : Bool) (m : ℕ) :=
  (gridUnitMatrixInputNatTrans (J i) (K i) (hX i) (hD i) m).naturality
    (𝟙 _ + oldContentInductionDotComponent mixedDatum mixedScalars (fun _ => 4) [false,true] i block)
example (i : Bool) (m : ℕ) :=
  (gridCapMatrixInputNatTrans (J i) (K i) (hX i) (hL i) m).naturality
    (𝟙 _ + oldContentInductionDotComponent mixedDatum mixedScalars (fun _ => 4) [false,true] i block)

/-- Generic endpoint adapters retain the already proved given module matrices. -/
example (i : Bool) := gridUnitMatrixInputComponentIso_hom
  (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [] i)
  (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [i] i)
  (oldContentMatrixCross_supernatural mixedDatum mixedScalars (fun _ => 4) [] i)
  (oldContentAppendDot_supernatural mixedDatum mixedScalars (fun _ => 4) [i] i) _ (pureUpper 0 i)
  (oldContentGridUnitMatrixIso mixedDatum mixedScalars (fun _ => 4) [] i (pureUpper 0 i) (unitSign i))
  (oldContentGridUnitMatrixIso_hom mixedDatum mixedScalars (fun _ => 4) [] i (pureUpper 0 i) (unitSign i))
example (i : Bool) := gridCapMatrixInputComponentIso_hom
  (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [i,i] i)
  (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [i,i,i] i)
  (oldContentMatrixCross_supernatural mixedDatum mixedScalars (fun _ => 4) [i,i] i)
  (oldContentAppendDot_supernatural mixedDatum mixedScalars (fun _ => 4) [i,i] i) _ (pureUpper 2 i)
  (oldContentGridCapMatrixIso mixedDatum mixedScalars (fun _ => 4) [i,i] i (pureUpper 2 i) (capSign i))
  (oldContentGridCapMatrixIso_hom mixedDatum mixedScalars (fun _ => 4) [i,i] i (pureUpper 2 i) (capSign i))

end GridMatrixFunctorConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixFunctor
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
