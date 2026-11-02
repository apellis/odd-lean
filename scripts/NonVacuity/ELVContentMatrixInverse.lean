import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
open CyclotomicAction.AsymmetricParameters
namespace ContentMatrixInverseConsumer
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
private def capTarget (i : Bool) : C 1 :=
  ⟨if i then [false, true, true, true, true] else [false, false, false, false, true]⟩
private def zeroTarget (i : Bool) : C 2 := ⟨[i]⟩

private theorem unitSign (i : Bool) :
    0 ≤ contentCrossingHeight mixedDatum (cutoff 4) i (unitTarget.word : Multiset Bool) := by
  cases i <;> norm_num [contentCrossingHeight, unitTarget, cutoff, mixedDatum, datum,
    SKM.Datum.h, SKM.Datum.α]
private theorem capSign (i : Bool) :
    contentCrossingHeight mixedDatum (cutoff 1) i ((capTarget i).word : Multiset Bool) ≤ 0 := by
  cases i <;> norm_num [contentCrossingHeight, capTarget, cutoff, mixedDatum, datum,
    SKM.Datum.h, SKM.Datum.α]
private theorem zeroSign (i : Bool) :
    contentCrossingHeight mixedDatum (cutoff 2) i ((zeroTarget i).word : Multiset Bool) = 0 := by
  cases i <;> norm_num [contentCrossingHeight, zeroTarget, cutoff, mixedDatum, datum,
    SKM.Datum.h, SKM.Datum.α]


private def unitObject : OldContentCategory mixedDatum mixedScalars (cutoff 4) unitTarget.word :=
  ⟨⟨[true, false]⟩, by simpa only [unitTarget, List.singleton_append] using (show ([true] ++ [false]).Perm ([false] ++ [true]) from List.perm_append_comm)⟩
private def capObject (i : Bool) :
    OldContentCategory mixedDatum mixedScalars (cutoff 1) (capTarget i).word :=
  ⟨capTarget i, List.Perm.refl _⟩
private def zeroObject (i : Bool) :
    OldContentCategory mixedDatum mixedScalars (cutoff 2) (zeroTarget i).word :=
  ⟨zeroTarget i, List.Perm.refl _⟩

/-- The full mixed representable gives both inverse products on actual content modules. -/
example (i : Bool) :
    let M := oldRepresentable mixedDatum mixedScalars (cutoff 4) (⟨[true, false]⟩ : C 4)
    let e := contentUnitMatrixIso mixedDatum mixedScalars (cutoff 4) M i unitTarget.word (unitSign i)
    e.hom ≫ e.inv = 𝟙 _ ∧ e.inv ≫ e.hom = 𝟙 _ ∧
      e.hom ∈ parity (R := ℚ) _ _ 0 ∧ e.inv ∈ parity (R := ℚ) _ _ 0 := by
  exact ⟨Iso.hom_inv_id _, Iso.inv_hom_id _, contentUnitMatrixIso_even _ _ _ _ _ _ _⟩

/-- No replacement or rescaling of the unit entries occurs in assembly. -/
example (i : Bool) :
    let M := oldRepresentable mixedDatum mixedScalars (cutoff 4) (⟨[true, false]⟩ : C 4)
    (contentUnitMatrixIso mixedDatum mixedScalars (cutoff 4) M i unitTarget.word (unitSign i)).hom.total
      unitObject = unitMatrixComponent mixedDatum mixedScalars (cutoff 4) i M
        (contentUnitCount mixedDatum (cutoff 4) i (unitTarget.word : Multiset Bool)) unitObject.obj :=
  contentUnitMatrixIso_hom_total _ _ _ _ _ _ _ _

/-- Negative height and both moving parities retain the cap entries. -/
example (i : Bool) :
    let M := oldRepresentable mixedDatum mixedScalars (cutoff 1) (capTarget i)
    (contentCapMatrixIso mixedDatum mixedScalars (cutoff 1) M i (capTarget i).word (capSign i)).hom.total
      (capObject i) = capMatrixComponent mixedDatum mixedScalars (cutoff 1) i M
        (contentCapCount mixedDatum (cutoff 1) i ((capTarget i).word : Multiset Bool)) (capTarget i) :=
  contentCapMatrixIso_hom_total _ _ _ _ _ _ _ _

/-- Inverse naturality along every arrow between arbitrary mixed-content endpoints. -/
example (i : Bool)
    (t t' : OldContentCategory mixedDatum mixedScalars (cutoff 4) unitTarget.word)
    (f : t ⟶ t') :
    let M := oldRepresentable mixedDatum mixedScalars (cutoff 4) (⟨[true, false]⟩ : C 4)
    let e := contentUnitMatrixNatIso mixedDatum mixedScalars (cutoff 4) M i unitTarget.word (unitSign i)
    (oldContentInclusion mixedDatum mixedScalars (cutoff 4) unitTarget.word ⋙
      ((BalancedInduction.restriction (append mixedDatum mixedScalars (cutoff 4) i)).obj
        ((BalancedInduction.induction (append mixedDatum mixedScalars (cutoff 4) i)).obj M)).toFunctor).map f ≫
      e.inv.app t' = e.inv.app t ≫
      (oldContentInclusion mixedDatum mixedScalars (cutoff 4) unitTarget.word ⋙
        (unitMatrixSourceModule mixedDatum mixedScalars (cutoff 4) M i
          (contentUnitCount mixedDatum (cutoff 4) i (unitTarget.word : Multiset Bool))).toFunctor).map f := by
  exact NatTrans.naturality _ f

/-- At height zero the finite count is zero and both module inversions remain valid. -/
example (i : Bool) :
    let M := oldRepresentable mixedDatum mixedScalars (cutoff 2) (zeroTarget i)
    let e := contentCapMatrixIso mixedDatum mixedScalars (cutoff 2) M i
      (zeroTarget i).word ((zeroSign i).le)
    e.hom ≫ e.inv = 𝟙 _ ∧ e.inv ≫ e.hom = 𝟙 _ ∧
      e.hom ∈ parity (R := ℚ) _ _ 0 ∧ e.inv ∈ parity (R := ℚ) _ _ 0 := by
  exact ⟨Iso.hom_inv_id _, Iso.inv_hom_id _, contentCapMatrixIso_even _ _ _ _ _ _ _⟩

example (i : Bool) : contentCapCount mixedDatum (cutoff 2) i
    ((zeroTarget i).word : Multiset Bool) = 0 := by
  unfold contentCapCount
  rw [zeroSign, neg_zero]
  rfl

end ContentMatrixInverseConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.Algebra.FiniteSupermodule,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixInverse] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
    let names := env.header.moduleData[idx]!.constNames
    unless names.size > 0 do throwError "Empty declaration inventory"
    for name in names do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited ALL {names.size} declarations in {owner}"
