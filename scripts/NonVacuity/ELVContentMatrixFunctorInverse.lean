import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixFunctorInverse
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
open CyclotomicAction.AsymmetricParameters
namespace ContentMatrixFunctorInverseConsumer
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
private def cutoff (n : ℕ) (_ : Bool) : ℕ := n
private abbrev C (n : ℕ) := OldCategory mixedDatum mixedScalars (cutoff n)
private def unitTarget : C 4 := ⟨[false, true]⟩
private def capTarget (i : Bool) : C 4 :=
  ⟨if i then [false, true, true, true, true, true] else [true, false, false, false, false, false]⟩
private def zeroTarget (i : Bool) : C 2 := ⟨[i]⟩

private theorem unitSign (i : Bool) :
    0 ≤ contentCrossingHeight mixedDatum (cutoff 4) i (unitTarget.word : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, unitTarget, cutoff, mixedDatum, datum,
    SKM.Datum.h, SKM.Datum.α]
private theorem capSign (i : Bool) :
    contentCrossingHeight mixedDatum (cutoff 4) i ((capTarget i).word : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, capTarget, cutoff, mixedDatum, datum,
    SKM.Datum.h, SKM.Datum.α]
private theorem zeroSign (i : Bool) :
    contentCrossingHeight mixedDatum (cutoff 2) i ((zeroTarget i).word : Multiset Bool) = 0 := by
  cases i <;> norm_num [contentCrossingHeight, zeroTarget, cutoff, mixedDatum, datum,
    SKM.Datum.h, SKM.Datum.α]


private def unitObject : OldContentCategory mixedDatum mixedScalars (cutoff 4) unitTarget.word :=
  ⟨⟨[true, false]⟩, by simpa only [unitTarget, List.singleton_append] using (show ([true] ++ [false]).Perm ([false] ++ [true]) from List.perm_append_comm)⟩
private def capObject (i : Bool) :
    OldContentCategory mixedDatum mixedScalars (cutoff 4) (capTarget i).word :=
  ⟨capTarget i, List.Perm.refl _⟩
private def M := oldRepresentable mixedDatum mixedScalars (cutoff 4) (⟨[true, false]⟩ : C 4)
private def N := oldRepresentable mixedDatum mixedScalars (cutoff 4) (⟨[false, true]⟩ : C 4)

private def capM (i : Bool) :=
  oldRepresentable mixedDatum mixedScalars (cutoff 4) (capTarget i)
private def capN (i : Bool) :=
  oldRepresentable mixedDatum mixedScalars (cutoff 4)
    (⟨if i then [true, false, true, true, true, true] else
      [false, true, false, false, false, false]⟩ : C 4)

/-- Whole matrix functor inversion, including both moving parities. -/
example (i : Bool) :
    let e := contentUnitMatrixFunctorNatIso mixedDatum mixedScalars (cutoff 4)
      i unitTarget.word (unitSign i)
    e.hom ≫ e.inv = 𝟙 _ ∧ e.inv ≫ e.hom = 𝟙 _ :=
  ⟨Iso.hom_inv_id _, Iso.inv_hom_id _⟩

/-- Both natural inverse directions are even as module morphisms. -/
example (i : Bool) :
    ((contentUnitMatrixFunctorNatIso mixedDatum mixedScalars (cutoff 4)
      i unitTarget.word (unitSign i)).hom.app M) ∈ parity (R := ℚ) _ _ 0 ∧
    ((contentUnitMatrixFunctorNatIso mixedDatum mixedScalars (cutoff 4)
      i unitTarget.word (unitSign i)).inv.app M) ∈ parity (R := ℚ) _ _ 0 :=
  contentUnitMatrixFunctorNatIso_even _ _ _ _ _ _ _

/-- Output permutation retains the literal, unrescaled unit matrix. -/
example (i : Bool) :
    ((contentUnitMatrixFunctorNatIso mixedDatum mixedScalars (cutoff 4)
      i unitTarget.word (unitSign i)).hom.app M).total unitObject =
      unitMatrixComponent mixedDatum mixedScalars (cutoff 4) i M
        (contentUnitCount mixedDatum (cutoff 4) i (unitTarget.word : Multiset Bool)) unitObject.obj :=
  contentUnitMatrixFunctorNatIso_hom_total _ _ _ _ _ _ _ _

/-- Inverses are natural in all input maps between mixed representables. -/
example (i : Bool) (f : M ⟶ N) :
    let e := contentUnitMatrixFunctorNatIso mixedDatum mixedScalars (cutoff 4)
      i unitTarget.word (unitSign i)
    (((BalancedInduction.induction (append mixedDatum mixedScalars (cutoff 4) i) ⋙
      BalancedInduction.restriction (append mixedDatum mixedScalars (cutoff 4) i)) ⋙
        BalancedInduction.restriction (oldContentInclusion mixedDatum mixedScalars (cutoff 4)
          unitTarget.word)).map f) ≫ e.inv.app N =
      e.inv.app M ≫ ((unitMatrixSourceFunctor mixedDatum mixedScalars (cutoff 4) i
        (contentUnitCount mixedDatum (cutoff 4) i (unitTarget.word : Multiset Bool)) ⋙
          BalancedInduction.restriction (oldContentInclusion mixedDatum mixedScalars (cutoff 4)
            unitTarget.word)).map f) := by
  exact NatTrans.naturality _ f

/-- The full finite source preserves the odd parity of a module map. -/
example (i : Bool) (f : M ⟶ N) (hf : f ∈ parity (R := ℚ) M N 1) :
    (unitMatrixSourceFunctor mixedDatum mixedScalars (cutoff 4) i 4).map f ∈
      parity (R := ℚ) _ _ 1 := IsSuperfunctor.map_mem hf

local instance : PiSupercategory ℚ (Superfunctor ℚ (C 4) (SVec ℚ)) :=
  supermodulePiSupercategory

/-- A literal odd parity-shift isomorphism supplies the odd map, with its parity proved. -/
example (i : Bool) :
    (unitMatrixSourceFunctor mixedDatum mixedScalars (cutoff 4) i 4).map
      ((SKM.homParityShiftDatum (k := ℚ) 1).iso M).inv ∈ parity (R := ℚ) _ _ 1 :=
  IsSuperfunctor.map_mem ((SKM.homParityShiftDatum (k := ℚ) 1).inv_mem M)

/-- Every finite cap row is retained at negative height, with both parities. -/
example (i : Bool) :
    let M := oldRepresentable mixedDatum mixedScalars (cutoff 4) (capTarget i)
    ((contentCapMatrixFunctorNatIso mixedDatum mixedScalars (cutoff 4)
      i (capTarget i).word (capSign i)).hom.app M).total (capObject i) =
      capMatrixComponent mixedDatum mixedScalars (cutoff 4) i M
        (contentCapCount mixedDatum (cutoff 4) i ((capTarget i).word : Multiset Bool)) (capTarget i) :=
  contentCapMatrixFunctorNatIso_hom_total _ _ _ _ _ _ _ _

/-- These negative-height blocks have nonempty finite cap families. -/
example (i : Bool) : 0 < contentCapCount mixedDatum (cutoff 4) i
    ((capTarget i).word : Multiset Bool) := by
  cases i <;> norm_num [contentCapCount, contentCrossingHeight, capTarget, cutoff,
    mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]

/-- Cap inverses also form a natural transformation on the full input category. -/
example (i : Bool) (f : capM i ⟶ capN i) :
    let e := contentCapMatrixFunctorNatIso mixedDatum mixedScalars (cutoff 4)
      i (capTarget i).word (capSign i)
    ((capMatrixTargetFunctor mixedDatum mixedScalars (cutoff 4) i
      (contentCapCount mixedDatum (cutoff 4) i ((capTarget i).word : Multiset Bool)) ⋙
        BalancedInduction.restriction (oldContentInclusion mixedDatum mixedScalars (cutoff 4)
          (capTarget i).word)).map f) ≫ e.inv.app (capN i) =
      e.inv.app (capM i) ≫ (((BalancedInduction.restriction
        (append mixedDatum mixedScalars (cutoff 4) i) ⋙ BalancedInduction.induction
          (append mixedDatum mixedScalars (cutoff 4) i)) ⋙
            BalancedInduction.restriction (oldContentInclusion mixedDatum mixedScalars (cutoff 4)
              (capTarget i).word)).map f) := by
  exact NatTrans.naturality _ f

/-- Zero count retains both functor inversions, including the principal mate. -/
example (i : Bool) :
    let e := contentUnitMatrixFunctorNatIso mixedDatum mixedScalars (cutoff 2)
      i (zeroTarget i).word ((zeroSign i).ge)
    let e' := contentCapMatrixFunctorNatIso mixedDatum mixedScalars (cutoff 2)
      i (zeroTarget i).word ((zeroSign i).le)
    e.hom ≫ e.inv = 𝟙 _ ∧ e'.inv ≫ e'.hom = 𝟙 _ :=
  ⟨Iso.hom_inv_id _, Iso.inv_hom_id _⟩

example (i : Bool) : contentUnitCount mixedDatum (cutoff 2) i
    ((zeroTarget i).word : Multiset Bool) = 0 := by
  unfold contentUnitCount
  rw [zeroSign]
  rfl

example (i : Bool) : contentCapCount mixedDatum (cutoff 2) i
    ((zeroTarget i).word : Multiset Bool) = 0 := by
  unfold contentCapCount
  rw [zeroSign, neg_zero]
  rfl

end ContentMatrixFunctorInverseConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.Algebra.FiniteSupermoduleFunctor,
      `OddMath.QuiverHecke.CyclotomicAction.ELVMatrixFunctorNaturality,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixFunctorInverse] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
    let names := env.header.moduleData[idx]!.constNames
    unless names.size > 0 do throwError "Empty declaration inventory"
    for name in names do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited ALL {names.size} declarations in {owner}"
