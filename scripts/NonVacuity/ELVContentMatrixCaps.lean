import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixCaps
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ContentMatrixCapsConsumer
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

example (i : Bool) := oldContentEFLinearEquiv_counit mixedDatum mixedScalars (fun _ => 4)
  [false, true] i (upperBlock i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false, true] i).obj source)

example (i : Bool) := oldContentEFLinearEquiv_dot mixedDatum mixedScalars (fun _ => 4)
  [false, true] i (upperBlock i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false, true] i).obj source)

example (i : Bool) (n : ℕ)
    (t : OldContentCategory mixedDatum mixedScalars (fun _ => 4) (i :: [false, true]))
    (x : BalancedInduction.Obj
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false, true] i)
      ((BalancedInduction.restriction
        (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false, true] i)).obj
          (upperBlock i)).toFunctor t) :=
  oldContentEFLinearEquiv_capDot mixedDatum mixedScalars (fun _ => 4) [false, true] i
    (upperBlock i) t n x

/-- In the odd case, both the coend coefficient and module vector have
identity and odd-dot parts. No homogeneous-vector premise is used. -/
example (i : Bool) (n : ℕ) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) [false, true] i (upperBlock i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false, true] i).obj source) n
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false, true] i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) [false, true] i)).obj
        (upperBlock i)).toFunctor source
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj v) +
      oldAppendDotComponent mixedDatum mixedScalars (fun _ => 4) i v)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj v) +
      oldAppendDotComponent mixedDatum mixedScalars (fun _ => 4) i v))

example (i : Bool) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i (pureUpper 0 i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i).obj (pureSource 0 i)) 0
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i)).obj
        (pureUpper 0 i)).toFunctor (pureSource 0 i)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource 0 i).obj))
    (pureVector 0 i))

example (i : Bool) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i (pureUpper 0 i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i).obj (pureSource 0 i)) 1
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i)).obj
        (pureUpper 0 i)).toFunctor (pureSource 0 i)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource 0 i).obj))
    (pureVector 0 i))

example (i : Bool) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i (pureUpper 0 i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i).obj (pureSource 0 i)) 2
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 0 i) i)).obj
        (pureUpper 0 i)).toFunctor (pureSource 0 i)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource 0 i).obj))
    (pureVector 0 i))

example (i : Bool) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i (pureUpper 1 i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i).obj (pureSource 1 i)) 0
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i)).obj
        (pureUpper 1 i)).toFunctor (pureSource 1 i)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource 1 i).obj))
    (pureVector 1 i))

example (i : Bool) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i (pureUpper 1 i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i).obj (pureSource 1 i)) 1
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i)).obj
        (pureUpper 1 i)).toFunctor (pureSource 1 i)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource 1 i).obj))
    (pureVector 1 i))

example (i : Bool) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i (pureUpper 1 i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i).obj (pureSource 1 i)) 2
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 1 i) i)).obj
        (pureUpper 1 i)).toFunctor (pureSource 1 i)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource 1 i).obj))
    (pureVector 1 i))

example (i : Bool) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i (pureUpper 2 i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i).obj (pureSource 2 i)) 0
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i)).obj
        (pureUpper 2 i)).toFunctor (pureSource 2 i)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource 2 i).obj))
    (pureVector 2 i))

example (i : Bool) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i (pureUpper 2 i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i).obj (pureSource 2 i)) 1
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i)).obj
        (pureUpper 2 i)).toFunctor (pureSource 2 i)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource 2 i).obj))
    (pureVector 2 i))

example (i : Bool) := oldContentEFLinearEquiv_capDot
  mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i (pureUpper 2 i)
  ((oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i).obj (pureSource 2 i)) 2
  (BalancedInduction.tensor
    (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i)
    ((BalancedInduction.restriction
      (oldContentAppend mixedDatum mixedScalars (fun _ => 4) (List.replicate 2 i) i)).obj
        (pureUpper 2 i)).toFunctor (pureSource 2 i)
    (𝟙 ((append mixedDatum mixedScalars (fun _ => 4) i).obj (pureSource 2 i).obj))
    (pureVector 2 i))

example (i : Bool) : contentCrossingHeight mixedDatum (fun _ => 4) i ([i] : Multiset Bool) = 2 := by
  norm_num [contentCrossingHeight, SKM.Datum.h, SKM.Datum.α,
    mixedDatum.cd.coroot_root_self]

example (i : Bool) : contentCrossingHeight mixedDatum (fun _ => 4) i ([i, i] : Multiset Bool) = 0 := by
  norm_num [contentCrossingHeight_coe, SKM.Datum.h, SKM.Datum.α,
    mixedDatum.cd.coroot_root_self]

example (i : Bool) : contentCrossingHeight mixedDatum (fun _ => 4) i ([i, i, i] : Multiset Bool) = -2 := by
  norm_num [contentCrossingHeight_coe, SKM.Datum.h, SKM.Datum.α,
    mixedDatum.cd.coroot_root_self]

end ContentMatrixCapsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixCaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
