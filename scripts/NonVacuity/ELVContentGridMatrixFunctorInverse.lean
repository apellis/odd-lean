import OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixFunctorInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ContentGridFunctorInverseConsumer
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

/-- Both signs, both moving parities, and exact prescribed forward module maps. -/
example (i : Bool) := oldContentGridUnitMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [] i (unitSign i)
example (i : Bool) := oldContentGridCapMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [i,i] i (capSign i)
example (i : Bool) := oldContentGridUnitMatrixFunctorNatIso_hom_app mixedDatum mixedScalars (fun _ => 4) [] i
  (unitSign i) (pureUpper 0 i)
example (i : Bool) := oldContentGridCapMatrixFunctorNatIso_hom_app mixedDatum mixedScalars (fun _ => 4) [i,i] i
  (capSign i) (pureUpper 2 i)
example (i : Bool) := oldContentGridUnitMatrixFunctorNatIso_even mixedDatum mixedScalars (fun _ => 4) [] i
  (unitSign i) (pureUpper 0 i)
example (i : Bool) := oldContentGridCapMatrixFunctorNatIso_even mixedDatum mixedScalars (fun _ => 4) [i,i] i
  (capSign i) (pureUpper 2 i)

/-- Both mate-only size-zero cases also retain the literal forward transformations. -/
example (i : Bool) := oldContentGridUnitMatrixFunctorNatIso_hom mixedDatum mixedScalars (fun _ => 4) [i] i
  (zeroUnitSign i)
example (i : Bool) := oldContentGridCapMatrixFunctorNatIso_hom mixedDatum mixedScalars (fun _ => 4) [i] i
  (zeroCapSign i)

private def oneBlock (i : Bool) :
    Superfunctor ℚ (OldContentCategory mixedDatum mixedScalars (fun _ => 4) [i]) (SVec ℚ) :=
  (BalancedInduction.restriction (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) [i])).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (pureSource 1 i).obj)
local notation "xd" i => oldContentInductionDotComponent mixedDatum mixedScalars (fun _ => 4) [i] i (oneBlock i)

/-- Naturality of both directions on the actual odd induced dot. -/
example (i : Bool) :=
  (oldContentGridUnitMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [i] i
    (zeroUnitSign i)).hom.naturality (xd i)
example (i : Bool) :=
  (oldContentGridUnitMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [i] i
    (zeroUnitSign i)).inv.naturality (xd i)
example (i : Bool) :=
  (oldContentGridCapMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [i] i
    (zeroCapSign i)).hom.naturality (xd i)
example (i : Bool) :=
  (oldContentGridCapMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [i] i
    (zeroCapSign i)).inv.naturality (xd i)

/-- Inhomogeneous input maps are covered without an evenness hypothesis. -/
example (i : Bool) :=
  (oldContentGridUnitMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [i] i
    (zeroUnitSign i)).hom.naturality (𝟙 _ + xd i)
example (i : Bool) :=
  (oldContentGridUnitMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [i] i
    (zeroUnitSign i)).inv.naturality (𝟙 _ + xd i)
example (i : Bool) :=
  (oldContentGridCapMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [i] i
    (zeroCapSign i)).hom.naturality (𝟙 _ + xd i)
example (i : Bool) :=
  (oldContentGridCapMatrixFunctorNatIso mixedDatum mixedScalars (fun _ => 4) [i] i
    (zeroCapSign i)).inv.naturality (𝟙 _ + xd i)

end ContentGridFunctorInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixFunctorInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
