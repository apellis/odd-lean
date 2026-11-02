import OddMath.QuiverHecke.CyclotomicAction.ELVMatrixEntryNaturality
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
open CyclotomicAction.AsymmetricParameters
namespace MatrixEntryNaturalityConsumer
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

private def M := oldRepresentable mixedDatum mixedScalars (cutoff 4) (⟨[true, false]⟩ : C 4)
private def N := oldRepresentable mixedDatum mixedScalars (cutoff 4) (⟨[false, true]⟩ : C 4)

/-- Both moving parities and every finite slot use the literal chosen entries. -/
example (i : Bool) (a : Option (Fin 4)) :
    (unitMatrixEntryNatTrans mixedDatum mixedScalars (cutoff 4) i 4 a).app M =
      eqToHom (unitMatrixSummandFunctor_obj mixedDatum mixedScalars (cutoff 4) i 4 a M) ≫
        unitMatrixEntry mixedDatum mixedScalars (cutoff 4) i M 4 a :=
  unitMatrixEntryNatTrans_app _ _ _ _ _ _ _

example (i : Bool) (a : Option (Fin 4)) :
    (capMatrixEntryNatTrans mixedDatum mixedScalars (cutoff 4) i 4 a).app M =
      capMatrixEntry mixedDatum mixedScalars (cutoff 4) i M 4 a ≫
        eqToHom (capMatrixSummandFunctor_obj mixedDatum mixedScalars (cutoff 4) i 4 a M).symm :=
  capMatrixEntryNatTrans_app _ _ _ _ _ _ _

/-- Input-module maps need no parity hypothesis after the source shift. -/
example (i : Bool) (a : Option (Fin 4)) (f : M ⟶ N) :
    (unitMatrixSummandFunctor mixedDatum mixedScalars (cutoff 4) i 4 a).map f ≫
      (unitMatrixEntryNatTrans mixedDatum mixedScalars (cutoff 4) i 4 a).app N =
    (unitMatrixEntryNatTrans mixedDatum mixedScalars (cutoff 4) i 4 a).app M ≫
      (BalancedInduction.induction (append mixedDatum mixedScalars (cutoff 4) i) ⋙
        BalancedInduction.restriction (append mixedDatum mixedScalars (cutoff 4) i)).map f :=
  NatTrans.naturality _ f

/-- Input-module maps need no parity hypothesis after the target shift either. -/
example (i : Bool) (a : Option (Fin 4)) (f : M ⟶ N) :
    (BalancedInduction.restriction (append mixedDatum mixedScalars (cutoff 4) i) ⋙
      BalancedInduction.induction (append mixedDatum mixedScalars (cutoff 4) i)).map f ≫
        (capMatrixEntryNatTrans mixedDatum mixedScalars (cutoff 4) i 4 a).app N =
    (capMatrixEntryNatTrans mixedDatum mixedScalars (cutoff 4) i 4 a).app M ≫
      (capMatrixSummandFunctor mixedDatum mixedScalars (cutoff 4) i 4 a).map f :=
  NatTrans.naturality _ f

/-- With no finite dotted slots the mate still defines the natural principal entry. -/
example (i : Bool) (f : M ⟶ N) :
    (unitMatrixSummandFunctor mixedDatum mixedScalars (cutoff 4) i 0 none).map f ≫
      (unitMatrixEntryNatTrans mixedDatum mixedScalars (cutoff 4) i 0 none).app N =
    (unitMatrixEntryNatTrans mixedDatum mixedScalars (cutoff 4) i 0 none).app M ≫
      (BalancedInduction.induction (append mixedDatum mixedScalars (cutoff 4) i) ⋙
        BalancedInduction.restriction (append mixedDatum mixedScalars (cutoff 4) i)).map f :=
  NatTrans.naturality _ f

/-- The unshifted odd third dot power keeps the Koszul sign against odd maps. -/
example (f : M ⟶ N) (hf : f ∈ parity (R := ℚ) M N 1) :
    (BalancedInduction.induction (append mixedDatum mixedScalars (cutoff 4) true)).map f ≫
        inductionDotModule mixedDatum mixedScalars (cutoff 4) true N ^ 3 =
      sign ℚ ((3 : ℕ) • mixedDatum.parity true * (1 : ZMod 2)) •
        ((inductionDotModule mixedDatum mixedScalars (cutoff 4) true M ^ 3) ≫
          (BalancedInduction.induction (append mixedDatum mixedScalars (cutoff 4) true)).map f) :=
  (inductionDotModule_power_supernatural mixedDatum mixedScalars (cutoff 4) true 3).naturality hf

end MatrixEntryNaturalityConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVMatrixEntryNaturality
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} declarations in {owner}"
