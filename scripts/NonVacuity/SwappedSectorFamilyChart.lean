import OddMath.QuiverHecke.SwappedAssembly.Sigma.SectorFamilyChart
import OddMath.QuiverHecke.SwappedAssembly.Sigma.MatrixEmbeddingEntries
import Mathlib.Algebra.Category.ModuleCat.Basic
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory OddMath.QuiverHecke.SwappedAssembly
open scoped ZeroObject
namespace SwappedSectorFamilyChartConsumer
open Classical
private def V (p : Bool → Prop) (_ : {a : Bool // p a}) : ModuleCat ℚ := ModuleCat.of ℚ ℚ
private def X (p : Bool → Prop) (n : ℕ) : Sum {a : Bool // p a} (Fin n) → ModuleCat ℚ :=
  Sum.elim (V p) (fun _ => ModuleCat.of ℚ ℚ)
private def chart (p : Bool → Prop) (n : ℕ) :=
  sectorFamilyIso p (Equiv.refl _) (X p n) (V p) (ModuleCat.of ℚ ℚ)
    (fun _ => Iso.refl _) (fun _ => Iso.refl _)
example (p : Bool → Prop) (n : ℕ) : (chart p n).hom ≫ (chart p n).inv = 𝟙 _ :=
  (chart p n).hom_inv_id
example (p : Bool → Prop) (n : ℕ) : (chart p n).inv ≫ (chart p n).hom = 𝟙 _ :=
  (chart p n).inv_hom_id
example := chart (fun _ => True) 2
example := chart (fun a => a = true) 2
example := chart (fun a => a = false) 2
example := chart (fun _ => True) 0
example := chart (fun a => a = true) 0
example := chart (fun a => a = false) 0
example : Limits.IsZero (sectorFamilyCorner (fun a => a = true) (V _) false) := by
  simpa only [sectorFamilyCorner, Bool.false_eq_true, dite_eq_right, not_false_eq_true] using
    Limits.isZero_zero (ModuleCat ℚ)
example : sectorFamilyCorner (fun a => a = true) (V _) true = ModuleCat.of ℚ ℚ := by
  simp [sectorFamilyCorner, V]
example (p q : Bool → Prop) (n m : ℕ) (f : famObj (X p n) ⟶ famObj (X q m))
    (j : Fin (Fintype.card (Sum {a : Bool // p a} (Fin n))))
    (k : Fin (Fintype.card (Sum {a : Bool // q a} (Fin m)))) :=
  matrixEmbeddingMap_apply
    (sectorFamilyObject (ι := Fin n) p (V p) (ModuleCat.of ℚ ℚ)) (famObj (X p n))
    (sectorFamilyObject (ι := Fin m) q (V q) (ModuleCat.of ℚ ℚ)) (famObj (X q m))
    (sectorFamilyEmbedding p (Equiv.refl _))
    (sectorFamilyEmbedding q (Equiv.refl _))
    (sectorFamilyComponentIso p (Equiv.refl _) (X p n) (V p) (ModuleCat.of ℚ ℚ)
      (fun _ => Iso.refl _) (fun _ => Iso.refl _))
    (sectorFamilyComponentIso q (Equiv.refl _) (X q m) (V q) (ModuleCat.of ℚ ℚ)
      (fun _ => Iso.refl _) (fun _ => Iso.refl _))
    (sectorFamily_missing_isZero p (Equiv.refl _) (V p) (ModuleCat.of ℚ ℚ))
    (sectorFamily_missing_isZero q (Equiv.refl _) (V q) (ModuleCat.of ℚ ℚ)) f j k
end SwappedSectorFamilyChartConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.Sigma.SectorFamilyChart,
      `OddMath.QuiverHecke.SwappedAssembly.Sigma.MatrixEmbeddingEntries] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
