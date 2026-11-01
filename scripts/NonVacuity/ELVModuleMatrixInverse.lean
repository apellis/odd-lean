import OddMath.QuiverHecke.CyclotomicAction.ELVModuleMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
open CyclotomicAction.AsymmetricParameters
namespace ModuleMatrixInverseConsumer
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

/-- Mixed colours, an arbitrary module, and the literal ordinary unit columns. -/
example (M : Superfunctor ℚ (C 4) (SVec ℚ)) (i : Bool) :
    (moduleUnitMatrixIso mixedDatum mixedScalars (cutoff 4) M i unitTarget (unitSign i)).hom =
      unitMatrixComponent mixedDatum mixedScalars (cutoff 4) i M
        (contentUnitCount mixedDatum (cutoff 4) i (unitTarget.word : Multiset Bool)) unitTarget :=
  moduleUnitMatrixIso_hom mixedDatum mixedScalars (cutoff 4) M i unitTarget (unitSign i)

example (M : Superfunctor ℚ (C 4) (SVec ℚ)) (i : Bool) :
    (moduleUnitMatrixIso mixedDatum mixedScalars (cutoff 4) M i unitTarget (unitSign i)).inv ∈
      parity (R := ℚ) (mateTargetSpace mixedDatum mixedScalars (cutoff 4) i M unitTarget)
        (unitMatrixSourceSpace mixedDatum mixedScalars (cutoff 4) i M
          (contentUnitCount mixedDatum (cutoff 4) i (unitTarget.word : Multiset Bool)) unitTarget) 0 :=
  moduleUnitMatrixIso_inv_even mixedDatum mixedScalars (cutoff 4) M i unitTarget (unitSign i)

/-- Both moving parities use the prescribed ordinary counit/dot rows on all modules. -/
example (M : Superfunctor ℚ (C 1) (SVec ℚ)) (i : Bool) :
    (moduleCapMatrixIso mixedDatum mixedScalars (cutoff 1) M i (capTarget i) (capSign i)).hom =
      capMatrixComponent mixedDatum mixedScalars (cutoff 1) i M
        (contentCapCount mixedDatum (cutoff 1) i ((capTarget i).word : Multiset Bool)) (capTarget i) :=
  moduleCapMatrixIso_hom mixedDatum mixedScalars (cutoff 1) M i (capTarget i) (capSign i)

example (M : Superfunctor ℚ (C 1) (SVec ℚ)) (i : Bool) :
    (moduleCapMatrixIso mixedDatum mixedScalars (cutoff 1) M i (capTarget i) (capSign i)).inv ∈
      parity (R := ℚ)
        (capMatrixTargetSpace mixedDatum mixedScalars (cutoff 1) i M
          (contentCapCount mixedDatum (cutoff 1) i ((capTarget i).word : Multiset Bool)) (capTarget i))
        (mateSourceSpace mixedDatum mixedScalars (cutoff 1) i M (capTarget i)) 0 :=
  moduleCapMatrixIso_inv_even mixedDatum mixedScalars (cutoff 1) M i (capTarget i) (capSign i)

/-- Height zero retains the exact two-sided inverse even with no cap slots. -/
example (M : Superfunctor ℚ (C 2) (SVec ℚ)) (i : Bool)
    (z : mateSourceSpace mixedDatum mixedScalars (cutoff 2) i M (zeroTarget i)) :
    (moduleCapMatrixIso mixedDatum mixedScalars (cutoff 2) M i (zeroTarget i)
      ((zeroSign i).le)).inv
      ((moduleCapMatrixIso mixedDatum mixedScalars (cutoff 2) M i (zeroTarget i)
        ((zeroSign i).le)).hom z) = z := by
  have h := congrArg
    (fun f : mateSourceSpace mixedDatum mixedScalars (cutoff 2) i M (zeroTarget i) ⟶
      mateSourceSpace mixedDatum mixedScalars (cutoff 2) i M (zeroTarget i) => f z)
    (moduleCapMatrixIso mixedDatum mixedScalars (cutoff 2) M i (zeroTarget i)
      ((zeroSign i).le)).hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h

end ModuleMatrixInverseConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleMatrixInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
